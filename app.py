import streamlit as st
import pandas as pd
import geopandas as gpd
from shapely.geometry import Polygon
import requests
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry
from bs4 import BeautifulSoup
from concurrent.futures import ThreadPoolExecutor, as_completed
import io
import re
import time
import threading
import tempfile
import os
import zipfile
import numpy as np

# Page Configuration
st.set_page_config(
    page_title="Lee County Property Intelligence Engine",
    page_icon="🏡",
    layout="wide"
)

DATALET_BASE_URL = "http://taxaccess.leecountync.gov/PT/Datalets/Datalet.aspx"
ARCGIS_PARCEL_URL = "https://lee-arcgis.leecountync.gov/arcgis/rest/services/Appraisal/APPRAISAL/MapServer/7/query"

# Spatial Analysis Endpoints
SPATIAL_ENDPOINTS = {
    "sewer_lines": [
        "https://lee-arcgis.leecountync.gov/arcgis/rest/services/ENERGOV26/Map/MapServer/19/query",
        "https://lee-arcgis.leecountync.gov/arcgis/rest/services/ENERGOV26/Map/MapServer/16/query"
    ],
    "sewer_manholes": "https://lee-arcgis.leecountync.gov/arcgis/rest/services/ENERGOV26/Map/MapServer/15/query",
    "water_lines": [
        "https://lee-arcgis.leecountync.gov/arcgis/rest/services/Appraisal/APPRAISAL/MapServer/14/query",
        "https://lee-arcgis.leecountync.gov/arcgis/rest/services/Appraisal/APPRAISAL/MapServer/15/query"
    ],
    "fema": "https://lee-arcgis.leecountync.gov/arcgis/rest/services/Appraisal/APPRAISAL/MapServer/5/query",
    "water_hydrant": "https://lee-arcgis.leecountync.gov/arcgis/rest/services/ENERGOV26/Map/MapServer/17/query"
}

TARGET_CRS = "EPSG:2264"  # NAD 1983 StatePlane North Carolina FIPS 3200 (US Feet)

HEADERS = {
    "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36"
}

RT_DATE_RE = re.compile(r'\b\d{1,2}[-/\s]?[A-Z]{3}[-/\s]?\d{2,4}\b|\b\d{1,2}[-/]\d{1,2}[-/]\d{2,4}\b', re.IGNORECASE)
NON_DIGIT_RE = re.compile(r'\D')

def format_pin_dashed(value):
    """Reconstructs the county's canonical dashed PIN format (e.g. '9660-90-1488-00') from any
    12-digit representation. The Lee County ArcGIS Parcels layer stores PIN exactly in this
    dashed 4-2-4-2 form, not as a plain 12-digit string, so a query using only digits never
    matches -- this is what actually makes the `PIN IN (...)` / `PIN LIKE` lookups hit."""
    digits = NON_DIGIT_RE.sub('', str(value)).zfill(12)
    if len(digits) != 12:
        return None
    return f"{digits[0:4]}-{digits[4:6]}-{digits[6:10]}-{digits[10:12]}"

SALE_FIELD_KEYS = ["sale_Date", "sale_Book", "sale_Page", "Sale_Instrument", "Sale_Price", "Sale_Validity_Code"]
RT_EXPECTED_HEADERS = ["date", "book", "page", "instrument", "sale price", "validity code"]

LUC_OPTIONS = [
    "101 - RESIDENTIAL", "110 - SINGLE FAMILY RESIDENCE(S)", "110E - DWELLING(S) OWNED BY NON PROFIT",
    "112 - MULTIFAMILY (DUPLEXES/TRIPLEXES=RES)", "113 - TOWNHOUSE / CONDOMINIUM", "403 - APTS - 40 OR MORE RENTAL UNITS",
    "APTS - APARTMENT(S) / MULTIFAMILY (COMMERCIAL)", "BANK - BANKS", "COM - COMMERCIAL - GENERAL",
    "COMD - HOUSE USED AS DAYCARE", "COML - COMMERCIAL LAND", "COMR - HOUSE USED AS COMMERCIAL",
    "COMS - HOUSE USED AS SALON", "CONS - HAS CONSERVATION EASMENT(S)", "DIST - DISTRIBUTION / WAREHOUSING",
    "FARM - FARMS (NO USE VAL)", "FRNL - FUNERAL SERVICES", "GOLF - GOLF COURSES / COUNTRY CLUBS",
    "HOSP - HOSPITALS", "HOTL - HOTELS / MOTELS", "HSEC - HOUSE USED AS COMM BLD", "IND - INDUSTRIAL",
    "INDL - INDUSTRIAL LAND", "INSL - INSTITUTIONAL LAND", "INST - INSTITUTIONAL", "MCOM - MISC COMMERCIAL",
    "MED - MEDICAL / DENTAL OFFICES", "MHP1 - MOBILE HOME PARKS", "MHP2 - MOBILE HOME PARKS + COMMERCIAL BLDGS",
    "MINE - MINING", "MINR - MINERAL RIGHTS", "MISC - MISC COMMERCIAL / INDUSTRIAL",
    "MIXD - COMMERCIAL AND RESIDENTIAL / RESIDENTIAL AND COMMERCIAL", "MULT - MULTIPLE COMMERCIAL USES",
    "NURS - NURSING HOMES", "OFFC - OFFICES - GENERAL", "PARK - COMMERCIAL PARKING AREA / DRIVEWAY",
    "PUBL - PUBLIC , COMMUNITY ASSEMBLY (TAXABLE)", "REC1 - SPORTS/RECREATION/GYM/HEALTH SPA",
    "REC2 - BOWLING ALLEYS / SKATING RINKS", "REST - RESTAURANTS / FAST FOODS / TAVERNS",
    "RET1 - RETAIL - GENERAL SINGLE TENNANT", "RET2 - RETAIL - MULTIPLE TENNANTS", "RET3 - RETAIL - STRIP SHOPPING",
    "RET4 - RETAIL - SHOPPING CENTER", "RET5 - CONVENIENCE STORES / GAS STATIONS", "RET6 - RETAIL - FOOD",
    "RET7 - RETAIL - AUTOMOTIVE / MARINE / CYCLES", "RET8 - RETAIL - MOBILE / MODULAR HOMES",
    "RET9 - RETAIL - BUILDING / FARM / NURSERIES", "RETO - RETAIL - OTHER / SPECIAL",
    "SGAR - SERVICE STATION / GARAGES / SHOPS", "SOLR - SOLAR FARM", "SPEC - SPECIAL COM/IND / PARTIAL EXEMPT",
    "TAIR - PRIVATE AIRPORT- TAXABLE", "TCEM - CEMETERIES - TAXABLE", "THER - THEATERS / CINIMAS",
    "TIMB - TIMBER PRODUCTION (NO UW)", "TPRP - PROPERTY OWNERS ASSOC-(TAXABLE)-COM / RES",
    "TPVT - PRIVATE EDUCATION / DAY CARES (TAXABLE)", "TREL - RELIGIOUS / CHURCHES - TAXABLE",
    "TRNS - TAXI / BUS STATIONS / TRANPORTATION", "TSCH - PRIVATE SCHOOLS - TAXABLE", "TVRD - TV / RADIO STATIONS",
    "UA - USE - AGRICULTURE", "UH - USE - HORTICULTURE", "UNDE - UNDEVELOPED VACANT LAND",
    "UTEL - ELECTRIC UTILITY", "UTGS - GAS UTILITY", "UTMS - MISC UTILITY", "UTPH - PHONE UTILITY",
    "UTRR - RAILROAD UTILITY", "UW - USE - FOREST", "VET - VETERINARY / KENNELS", "WATR - WATER",
    "WHSE - WAREHOUSING / STORAGE SERVISES", "WIND - WIND TURBINE", "XAIR - MUNICIPAL AIRPORT",
    "XBWY - BROADWAY MUNICIPAL", "XCEM - CEMETERIES - EXEMPT", "XCOM - MISC COMM / IND EXEMPT",
    "XGOV - COUNTY GOVERNMENTAL", "XHSA - HOUSING AUTHORITY", "XJAL - CORRECTIONAL",
    "XLEE - LEE COUNTY MUNICIPLE", "XLFL - COUNTY / CITY LANDFILLS", "XLOD - CLUBS / LODGES / FRATL/COMMUNITY (EX)",
    "XLUT - LEE COUNTY UTILITY", "XMUN - FIRE / RESCUE / POLICE STATIONS", "XNCS - NC STATE",
    "XNPR - MISC NON-PROFIT EXEMPT", "XPRK - PARKS - EXEMPT", "XPRP - PROPERTY ASSOCIATIONS",
    "XPVT - PRIVATE EDUCATION / DAY CARES (EXEMPT)", "XREL - RELIGIOUS / CHURCHES - EXEMPT",
    "XRES - EXEMPT RESIDENTIAL", "XSAN - SANFORD MUNICIPAL", "XSCH - COUNTY SCHOOLS",
    "XSUT - SANFORD UTILITY", "XUVY - COLLEGES / UNIVERSITIES"
]

thread_local = threading.local()

def get_http_session():
    if not hasattr(thread_local, "session"):
        session = requests.Session()
        adapter = HTTPAdapter(
            pool_connections=50,
            pool_maxsize=100,
            max_retries=Retry(total=2, backoff_factor=0.2, status_forcelist=[500, 502, 503, 504])
        )
        session.mount("http://", adapter)
        session.mount("https://", adapter)
        thread_local.session = session
    return thread_local.session

def fetch_parcels_from_arcgis(min_acres=0.0, max_acres=999999.0, status_cb=None):
    """Broad acreage-range parcel query against the county-wide Parcels layer. This is an
    intentionally wide query (used only for the explicit 'Spatial Filter' data-source mode) and
    must ONLY ever be invoked in direct response to the user pressing Start/Run -- never on
    script load or on an unrelated rerun, since a script rerun happens on almost any widget
    interaction in Streamlit and re-triggering a county-wide paginated fetch on every one of
    those would be both slow and wasteful."""
    session = get_http_session()
    where_clause = f"ACRES >= {min_acres} AND ACRES <= {max_acres}"
    all_features = []
    batch_size = 1000
    offset = 0

    while True:
        params = {
            "where": where_clause,
            "outFields": "PIN,ACRES",
            "returnGeometry": "true",
            "outSR": "4326",
            "resultRecordCount": batch_size,
            "resultOffset": offset,
            "f": "geojson"
        }
        try:
            response = session.get(ARCGIS_PARCEL_URL, params=params, timeout=30)
            if response.status_code == 200:
                data = response.json()
                features = data.get("features", [])
                if not features:
                    break
                all_features.extend(features)
                if status_cb:
                    status_cb(len(all_features))
                if len(features) < batch_size and not data.get("exceededTransferLimit"):
                    break
                offset += batch_size
            else:
                break
        except Exception as e:
            st.warning(f"ArcGIS Pagination Warning: {e}")
            break

    if all_features:
        gdf = gpd.GeoDataFrame.from_features(all_features)
        gdf.set_crs("EPSG:4326", allow_override=True, inplace=True)
        return gdf.to_crs(TARGET_CRS)

    return gpd.GeoDataFrame(columns=["PIN", "ACRES", "geometry"], geometry=[], crs=TARGET_CRS)

def fetch_parcels_by_pins(pins, batch_size=100):
    """Targeted geometry fetch for a SPECIFIC list of PINs (e.g. from an uploaded CSV, or from
    completed lookup results), instead of pulling the entire county. Queried via POST (not GET --
    a GET with 100-400 quoted PIN values in the URL can silently exceed the ArcGIS server's URL
    length limit and get rejected, which a bare `except: continue` would swallow without a trace).
    Tries an exact `PIN IN (...)` match against both the raw PIN string and the cleaned/
    zero-padded version first; if that returns nothing, falls back to a `LIKE` match on the
    digit-only PIN in case the layer stores PINs in a different format (dashes, different
    padding, etc.) than either of those. Returns (GeoDataFrame, list_of_error_strings) so the
    caller can show the *actual* reason a fetch failed instead of a generic message."""
    session = get_http_session()
    errors = []

    def _run_query(where):
        params = {
            "where": where,
            "outFields": "PIN,ACRES",
            "returnGeometry": "true",
            "outSR": "4326",
            "f": "geojson",
        }
        try:
            resp = session.post(ARCGIS_PARCEL_URL, data=params, timeout=30)
        except Exception as e:
            errors.append(f"Request failed: {e}")
            return []
        if resp.status_code != 200:
            errors.append(f"HTTP {resp.status_code}: {resp.text[:300]}")
            return []
        try:
            payload = resp.json()
        except Exception:
            errors.append(f"Non-JSON response: {resp.text[:300]}")
            return []
        if "error" in payload:
            errors.append(f"ArcGIS error: {payload['error']}")
            return []
        return payload.get("features", [])

    candidates = set()
    for p in pins:
        if not p:
            continue
        raw = str(p).strip()
        if raw:
            candidates.add(raw)
        cleaned = NON_DIGIT_RE.sub('', raw).zfill(12)
        if cleaned:
            candidates.add(cleaned)
        dashed = format_pin_dashed(raw)
        if dashed:
            candidates.add(dashed)
    candidates = list(candidates)

    all_features = []
    for i in range(0, len(candidates), batch_size):
        batch = candidates[i:i + batch_size]
        pin_sql = ",".join("'" + p.replace("'", "''") + "'" for p in batch)
        all_features.extend(_run_query(f"PIN IN ({pin_sql})"))

    if not all_features and candidates:
        # Fallback: exact IN() found nothing -- try LIKE against BOTH the digit-only PIN and the
        # dashed format, in case the layer's stored PIN format differs from all of the above.
        # (A digit-only LIKE alone can't match a dashed value like '9660-90-1488-00', since the
        # dashes break up the substring -- so the dashed form has to be tried too.)
        like_targets = set()
        for p in pins:
            if not p:
                continue
            d = NON_DIGIT_RE.sub('', str(p))
            if d:
                like_targets.add(d)
            dashed = format_pin_dashed(p)
            if dashed:
                like_targets.add(dashed)
        like_targets = sorted(like_targets)
        like_batch_size = 25  # LIKE-chain WHERE clauses are heavier; keep batches smaller
        for i in range(0, len(like_targets), like_batch_size):
            batch = like_targets[i:i + like_batch_size]
            like_clause = " OR ".join(f"PIN LIKE '%{t}%'" for t in batch)
            if like_clause:
                all_features.extend(_run_query(like_clause))

    if all_features:
        gdf = gpd.GeoDataFrame.from_features(all_features)
        gdf.set_crs("EPSG:4326", allow_override=True, inplace=True)
        gdf = gdf.drop_duplicates(subset=["PIN"]) if "PIN" in gdf.columns else gdf
        return gdf.to_crs(TARGET_CRS), errors

    return gpd.GeoDataFrame(columns=["PIN", "ACRES", "geometry"], geometry=[], crs=TARGET_CRS), errors

def fetch_arcgis_layer_to_gdf(url):
    """Fetches an entire ArcGIS layer (sewer/water lines, manholes, hydrants, FEMA), paginated.

    IMPORTANT: ArcGIS Server enforces its own maxRecordCount per layer, independent of whatever
    resultRecordCount we ask for -- a layer capped at 1000 will silently return at most 1000
    features per call even if we request 2000, and flags this via `exceededTransferLimit: true`
    in the response. The previous version only checked `len(features) < batch_size` to decide
    when to stop, so on a layer with a lower server-side cap it would stop after page ONE,
    silently discarding the rest of the layer county-wide. That directly corrupts every distance
    calculation downstream (a "nearest line" search run against an incomplete subset of lines can
    only ever report a distance >= the true nearest distance), which is almost certainly the
    source of large discrepancies against ArcGIS's own Near / Generate Near Table results. This
    version pages by however many features actually came back, and keeps going as long as either
    a full page came back OR the server explicitly says there's more."""
    session = get_http_session()
    all_features = []
    offset = 0
    batch_size = 2000
    while True:
        params = {
            "where": "1=1",
            "outFields": "*",
            "returnGeometry": "true",
            "outSR": "4326",
            "resultRecordCount": batch_size,
            "resultOffset": offset,
            "f": "geojson"
        }
        try:
            resp = session.get(url, params=params, timeout=30)
        except Exception:
            break
        if resp.status_code != 200:
            break
        try:
            data = resp.json()
        except Exception:
            break
        features = data.get("features", [])
        if not features:
            break
        all_features.extend(features)
        if len(features) < batch_size and not data.get("exceededTransferLimit"):
            break
        offset += len(features)  # advance by what actually came back, not the requested batch_size
    if all_features:
        gdf = gpd.GeoDataFrame.from_features(all_features)
        if gdf.crs is None:
            gdf.set_crs("EPSG:4326", allow_override=True, inplace=True)
        return gdf.to_crs(TARGET_CRS)

    return gpd.GeoDataFrame(columns=["geometry"], geometry=[], crs=TARGET_CRS)

def compute_intersect_and_distance(base_gdf, target_gdf):
    """Given base_gdf (parcel polygons) and target_gdf (a line or point layer), returns two
    Series aligned to base_gdf.index: a boolean 'does any target feature intersect/touch this
    parcel' and the minimum distance (in the base CRS's linear unit -- feet, here) to the
    nearest target feature. Used identically for sewer lines, sewer manholes, water lines, and
    water hydrants so each layer gets its OWN intersect flag and distance, computed
    independently -- not shared/derived from each other."""
    if target_gdf is None or target_gdf.empty:
        return pd.Series(False, index=base_gdf.index), pd.Series(np.nan, index=base_gdf.index)
    joined = gpd.sjoin(base_gdf[["geometry"]], target_gdf[["geometry"]], how="left", predicate="intersects")
    intersects = joined.groupby(level=0)["index_right"].apply(lambda s: s.notna().any()).reindex(base_gdf.index, fill_value=False)
    distances = base_gdf.geometry.apply(lambda geom: target_gdf.distance(geom).min())
    return intersects, distances

def extract_specific_fields(clean_pin, tax_year):
    session = get_http_session()
    main_params = {"mode": "", "UseSearch": "no", "pin": clean_pin, "jur": "000", "taxyr": tax_year}
    try:
        resp_main = session.get(DATALET_BASE_URL, params=main_params, headers=HEADERS, timeout=8)
    except Exception as e:
        return {"Status": f"HTTP Error: {str(e)}"}

    if "Problem encountered rendering" in resp_main.text or "No Data" in resp_main.text:
        return {"Status": "Not Found / Invalid PIN"}

    try:
        soup_main = BeautifulSoup(resp_main.text, 'lxml')
    except Exception:
        soup_main = BeautifulSoup(resp_main.text, 'html.parser')

    extracted = {"Status": "Success"}

    def get_val_from_soup(soup_obj, label_patterns):
        if not soup_obj: return ""
        if isinstance(label_patterns, str): label_patterns = [label_patterns]
        try:
            for pattern in label_patterns:
                element = soup_obj.find(string=lambda t: t and re.search(re.escape(pattern), t, re.IGNORECASE))
                if element:
                    parent_tr = element.find_parent("tr")
                    if parent_tr:
                        cols = parent_tr.find_all(["th", "td"])
                        for idx, col in enumerate(cols):
                            col_text = col.text.strip().replace("\xa0", " ")
                            if element in col.find_all(string=True) or pattern.lower() in col_text.lower():
                                if idx + 1 < len(cols):
                                    val = cols[idx + 1].text.strip().replace("\xa0", " ")
                                    if val and len(val) < 200: return val
        except Exception:
            pass
        return ""

    def get_mailing_address(soup):
        try:
            owner_table = soup.find('table', id='Owner') or soup.find('table', id='Owner Details')
            if not owner_table:
                for t in soup.find_all('table'):
                    if "Mailing Address" in t.text:
                        owner_table = t
                        break
            if owner_table:
                rows = owner_table.find_all('tr')
                address_lines = []
                capturing = False
                stop_keywords = ["OWNER", "ACCOUNT", "NAME", "OWN %", "LINKED SALE", "ADDITIONAL OWNERS", "TAX YEAR"]
                for r in rows:
                    cells = r.find_all(['th', 'td'])
                    if len(cells) >= 2:
                        label_text = cells[0].text.strip().replace("\xa0", " ")
                        val_text = cells[1].text.strip().replace("\xa0", " ")
                        if re.search(r'Mailing\s*Address', label_text, re.IGNORECASE):
                            capturing = True
                            if val_text: address_lines.append(val_text)
                            continue
                        if capturing:
                            if any(k in label_text.upper() for k in stop_keywords) and not re.search(r'ADDRESS|CITY|STATE|ZIP', label_text.upper()):
                                break
                            if val_text: address_lines.append(val_text)
                if address_lines: return ", ".join([l for l in address_lines if l])
        except Exception:
            pass
        return ""

    def get_plat_info(soup_list):
        cab, slide, combined = "", "", ""
        for soup in soup_list:
            if not soup:
                continue
            for tr in soup.find_all("tr"):
                cells = tr.find_all(["th", "td"])
                if len(cells) < 2:
                    continue
                label = cells[0].text.strip().replace("\xa0", " ").lower()
                val = cells[1].text.strip().replace("\xa0", " ")
                if not val or "plat" not in label:
                    continue
                if ("cabinet" in label and "slide" in label) or ("book" in label and "page" in label):
                    combined = val
                elif "cabinet" in label or "book" in label:
                    cab = val
                elif "slide" in label or "page" in label:
                    slide = val
            if combined:
                return combined
            if cab or slide:
                return f"{cab}/{slide}".strip("/")
        return ""

    def _norm_header(s): return re.sub(r'\s+', ' ', s.strip().lower())
    def _direct_rows(table): return [tr for tr in table.find_all("tr") if tr.find_parent("table") is table]

    def parse_recorded_transaction(soup_obj):
        empty_res = {k: "" for k in SALE_FIELD_KEYS}
        if not soup_obj: return empty_res, False
        candidates = []
        for table in soup_obj.find_all("table"):
            rows = _direct_rows(table)
            if len(rows) < 2: continue
            for h_idx, header_row in enumerate(rows[:-1]):
                header_cells = [_norm_header(c.text.replace("\xa0", " ")) for c in header_row.find_all(["th", "td"])]
                if len(header_cells) < 6: continue
                if all(exp in header_cells[i] for i, exp in enumerate(RT_EXPECTED_HEADERS)):
                    candidates.append((table, h_idx, rows))
        for _, h_idx, rows in candidates:
            for data_row in rows[h_idx + 1:]:
                cell_vals = [c.text.strip().replace("\xa0", " ") for c in data_row.find_all(["td", "th"])]
                if not cell_vals or _norm_header(cell_vals[0]) == "date": continue
                while len(cell_vals) < 6: cell_vals.append("")
                if RT_DATE_RE.search(cell_vals[0].upper()):
                    return dict(zip(SALE_FIELD_KEYS, cell_vals[:6])), True
                break
        return empty_res, False

    def fetch_transaction_data(clean_pin, tax_year, soup_main):
        trans, found = parse_recorded_transaction(soup_main)
        if found: return trans, None
        soup_sales = None
        try:
            r_sales = session.get(DATALET_BASE_URL, params={"mode": "sales", "UseSearch": "no", "pin": clean_pin, "jur": "000", "taxyr": tax_year}, headers=HEADERS, timeout=6)
            soup_sales = BeautifulSoup(r_sales.text, 'html.parser')
            trans, found = parse_recorded_transaction(soup_sales)
            if found: return trans, soup_sales
        except Exception:
            pass
        try:
            r_deed = session.get(DATALET_BASE_URL, params={"mode": "deed", "UseSearch": "no", "pin": clean_pin, "jur": "000", "taxyr": tax_year}, headers=HEADERS, timeout=6)
            soup_deed = BeautifulSoup(r_deed.text, 'html.parser')
            trans, found = parse_recorded_transaction(soup_deed)
            if found: return trans, soup_deed
        except Exception:
            pass
        return trans, soup_sales

    sales_info, soup_supplemental = fetch_transaction_data(clean_pin, tax_year, soup_main)

    soup_bldg = None
    living_units_val = get_val_from_soup(soup_main, ["Living Units", "No. Units", "Units", "Total Units"])
    if not living_units_val:
        try:
            r_bldg = session.get(DATALET_BASE_URL, params={"mode": "resbldg", "UseSearch": "no", "pin": clean_pin, "jur": "000", "taxyr": tax_year}, headers=HEADERS, timeout=6)
            soup_bldg = BeautifulSoup(r_bldg.text, 'html.parser')
            living_units_val = get_val_from_soup(soup_bldg, ["Living Units", "No. Units", "Units", "Residential Units"])
        except Exception:
            pass

    extracted["Tax_Year"] = get_val_from_soup(soup_main, "Tax Year")
    extracted["Jurisdiction"] = get_val_from_soup(soup_main, ["Tax Jurisdiction", "Jurisdiction"])
    extracted["Neighborhood"] = get_val_from_soup(soup_main, "Neighborhood")
    extracted["Appraised_Land"] = get_val_from_soup(soup_main, "Appraised Land")
    extracted["Appraised_Building"] = get_val_from_soup(soup_main, "Appraised Building")
    extracted["Appraised_Total"] = get_val_from_soup(soup_main, "Appraised Total")
    extracted["Deferred"] = get_val_from_soup(soup_main, "Deferred")
    extracted["Exempts_Excluded"] = get_val_from_soup(soup_main, ["Exempts/Excluded", "Exemptions"])
    extracted["Assessed_Real"] = get_val_from_soup(soup_main, "Assessed Real")
    extracted["Total_Assessed"] = get_val_from_soup(soup_main, "Total Assessed")
    extracted["Account_Number"] = get_val_from_soup(soup_main, ["Account Number", "Account"])
    extracted["Owner_Name"] = get_val_from_soup(soup_main, ["Name:", "Owner Name", "Name"])
    extracted["Owner_Name_2"] = get_val_from_soup(soup_main, "Name 2:")
    extracted["Own_Percent"] = get_val_from_soup(soup_main, "Own %")
    extracted["Mailing_Address"] = get_mailing_address(soup_main)
    extracted["Linked_Sale"] = get_val_from_soup(soup_main, "Linked Sale")
    extracted["Physical_Address"] = get_val_from_soup(soup_main, ["Physical Address", "Location Address", "Site Address"])
    extracted["Legal_Description"] = get_val_from_soup(soup_main, "Legal Description")
    extracted["Plat Cabinet/Slide"] = get_plat_info([soup_main, soup_supplemental, soup_bldg])
    extracted["NBHD_Code_Name"] = get_val_from_soup(soup_main, ["NBHD Code / Name", "NBHD Code"])
    extracted["Class"] = get_val_from_soup(soup_main, "Class:")
    extracted["Land_Use"] = get_val_from_soup(soup_main, "Land Use:")
    extracted["Zoning"] = get_val_from_soup(soup_main, "Zoning:")
    extracted["Living_Units"] = living_units_val
    extracted["Deeded_Acres"] = get_val_from_soup(soup_main, "Deeded Acres")
    extracted["Calculated_Acres"] = get_val_from_soup(soup_main, "Calculated Acres")
    extracted.update(sales_info)
    return extracted

def fetch_single_parcel(row_idx, raw_pin, tax_year):
    clean_pin = NON_DIGIT_RE.sub('', str(raw_pin)).zfill(12)
    record = {"Input_PIN": str(raw_pin), "Clean_PIN": clean_pin}
    try:
        record.update(extract_specific_fields(clean_pin, tax_year))
    except Exception as e:
        record["Status"] = f"Error: {str(e)}"
    return row_idx, record

# --- Compact Commercial Styling (matches the target dashboard mockup) ---
st.markdown("""
    <style>
    .stApp { background-color: #f5f6f8; }
    .block-container { padding-top: 1.4rem; padding-bottom: 2rem; }

    /* App header */
    .app-header { display:flex; align-items:center; gap:12px; padding-bottom: 16px; margin-bottom: 18px; border-bottom: 1px solid #e5e7eb; }
    .app-header .title { font-size: 20px; font-weight: 700; color: #14181f; line-height:1.2; }
    .app-header .subtitle { color: #6b7280; font-size: 13px; margin-top: 1px; }

    /* Cards */
    .card {
        background-color: #ffffff;
        padding: 18px 20px;
        border-radius: 12px;
        box-shadow: 0 1px 3px rgba(16,24,40,0.05);
        border: 1px solid #e5e7eb;
        margin-bottom: 14px;
    }
    .card-title { font-size: 15px; font-weight: 700; color: #14181f; margin: 0 0 2px 0; display:flex; align-items:center; gap:8px; }
    .card-subtext { color: #6b7280; font-size: 13px; margin-bottom: 14px; }

    /* Nested status box (e.g. "Ready for extraction") */
    .status-box { border: 1px solid #e5e7eb; border-radius: 10px; padding: 14px 16px; background: #fafbfc; }
    .status-box .status-label { font-weight: 700; font-size: 14px; color: #14181f; margin-bottom: 8px; }
    .status-box .status-readout { border: 1px solid #e5e7eb; border-radius: 8px; background: #ffffff; padding: 10px 12px; color: #6b7280; font-size: 13px; min-height: 20px; }

    /* Buttons */
    .stButton>button { border-radius: 8px; font-weight: 600; transition: all 0.15s ease-in-out; height: 3rem; }
    div.stButton { margin-top: 2px; }
    .btn-anchor { display:none; }
    .btn-anchor-start + div.stButton button { background-color: #2952e3; color: #fff; border: 1px solid #2952e3; }
    .btn-anchor-start + div.stButton button:hover:not(:disabled) { background-color: #1f3fc0; border-color:#1f3fc0; }
    .btn-anchor-stop + div.stButton button { background-color: #fff; color: #384152; border: 1px solid #d0d5dd; }
    .btn-anchor-rerun + div.stButton button { background-color: #fff; color: #d92d20; border: 1px solid #f4a19a; }
    .btn-anchor-rerun + div.stButton button:hover:not(:disabled) { background-color: #fef3f2; }
    div.stButton button:disabled { opacity: 0.45; cursor: not-allowed; }

    /* KPI tiles */
    .kpi-row { display:flex; gap:14px; margin: 14px 0; }
    .kpi-tile { flex:1; background: #ffffff; border: 1px solid #e5e7eb; border-radius: 12px; box-shadow: 0 1px 3px rgba(16,24,40,0.05); padding: 16px 18px; display:flex; align-items:center; gap:12px; }
    .kpi-icon { width:38px; height:38px; border-radius:50%; display:flex; align-items:center; justify-content:center; font-size:17px; flex-shrink:0; }
    .kpi-icon.blue { background:#e8edfc; }
    .kpi-icon.green { background:#e6f6ec; }
    .kpi-icon.orange { background:#fdf1e3; }
    .kpi-icon.purple { background:#f1eafc; }
    .kpi-value { font-size: 22px; font-weight: 700; color: #14181f; line-height:1.1; }
    .kpi-label { font-size: 13px; font-weight: 600; color: #384152; margin-top:1px; }
    .kpi-sublabel { font-size: 11px; color: #9aa2b1; margin-top:1px; }

    /* Info banner */
    .info-banner { background:#eaf2fd; border:1px solid #cfe2fb; border-radius:10px; padding:12px 16px; font-size:13px; color:#1a4480; margin-top: 6px; }
    .info-banner .link-line { color:#2952e3; font-weight:600; margin-top:4px; }

    /* Sidebar */
    section[data-testid="stSidebar"] .block-container { padding-top: 1.2rem; }
    .sidebar-section-label { font-size: 11px; font-weight: 700; letter-spacing: 0.06em; color: #6b7280; text-transform: uppercase; margin: 16px 0 8px 0; }
    .sidebar-section-label:first-of-type { margin-top: 0; }
    .config-row-label { font-size: 13.5px; font-weight: 600; color: #384152; }
    .value-chip { border:1px solid #d0d5dd; border-radius:6px; padding: 3px 10px; text-align:center; font-weight:600; font-size:13px; color:#14181f; background:#fff; }
    hr.sidebar-divider { border: none; border-top: 1px solid #e5e7eb; margin: 14px 0; }

    div[data-testid="stExpander"] { border: 1px solid #e5e7eb !important; border-radius: 10px !important; box-shadow: none !important; margin-bottom: 8px; }
    div[data-testid="stExpander"] summary { padding: 10px 12px !important; font-weight: 600 !important; font-size: 13.5px !important; color: #384152 !important; }

    div[data-testid="stFileUploaderDropzone"] { border-radius: 10px !important; }
    </style>
""", unsafe_allow_html=True)

st.markdown("""
    <div class="app-header">
        <span style="font-size:28px;">🏠</span>
        <div>
            <div class="title">Property Intelligence Engine</div>
            <div class="subtitle">Lee County, NC &bull; 2026 Assessment</div>
        </div>
    </div>
""", unsafe_allow_html=True)

TAX_YEAR = "2026"  # Assessment year is fixed -- no longer user-selectable

# --- Sidebar Configuration (grouped into expanders to cut down scroll height) ---
with st.sidebar:
    st.markdown('<div class="sidebar-section-label">Engine Configuration</div>', unsafe_allow_html=True)
    if "max_workers" not in st.session_state:
        st.session_state.max_workers = 40
    col_lbl, col_val = st.columns([3, 1])
    with col_lbl:
        st.markdown('<div class="config-row-label" style="padding-top:6px;">Processing Capacity</div>', unsafe_allow_html=True)
    with col_val:
        st.markdown(f'<div class="value-chip">{st.session_state.max_workers}</div>', unsafe_allow_html=True)
    max_workers = st.slider("Processing Capacity", min_value=10, max_value=100, step=5, key="max_workers", label_visibility="collapsed")
    st.caption(f"Assessment year is fixed to {TAX_YEAR}.")

    st.markdown('<hr class="sidebar-divider">', unsafe_allow_html=True)
    st.markdown('<div class="sidebar-section-label">Data Source</div>', unsafe_allow_html=True)
    st.markdown('<div class="config-row-label">Upload parcel list (CSV)</div>', unsafe_allow_html=True)
    uploaded_file = st.file_uploader("Upload parcel list (CSV)", type=["csv"], label_visibility="collapsed")
    include_shapes = st.checkbox(
        "Include parcel geometries", value=True,
        help="Fetches ArcGIS parcel polygons ONLY for the PINs in your result set -- required for shape exports and spatial analysis."
    )
    if uploaded_file is None:
        st.caption("Parcels will be pulled from ArcGIS using the Area filter below, but only once you press **Start Extraction**.")

    with st.expander("📐 Area Filter", expanded=False):
        use_area_filter = st.checkbox("Enable Area Filter", value=False)
        min_area_val, max_area_val = 0.0, 100000.0
        area_unit = "SqFt"
        if use_area_filter:
            area_unit = st.radio("Area Unit", ["SqFt", "Acres"], horizontal=True)
            col_a1, col_a2 = st.columns(2)
            with col_a1: min_area_val = st.number_input("Min Area", value=0.0, step=100.0)
            with col_a2: max_area_val = st.number_input("Max Area", value=50000.0, step=500.0)

    with st.expander("🗂️ Land Use", expanded=False):
        selected_lucs = st.multiselect("Select Land Use Code(s) (LUC)", options=LUC_OPTIONS, default=[], label_visibility="collapsed")

    with st.expander("⚙️ Spatial Analysis", expanded=False):
        analysis_options = st.multiselect(
            "Select Analysis Type(s)",

            ["Sewer Analysis", "Water Analysis", "FEMA Analysis"],
            default=[], label_visibility="collapsed"
        )
        if analysis_options and not include_shapes:
            st.caption("⚠️ Enable 'Include Polygon Geometries' above to run these.")

# Initialize Session States
if "master_results" not in st.session_state: st.session_state.master_results = []
if "is_running" not in st.session_state: st.session_state.is_running = False
if "is_paused" not in st.session_state: st.session_state.is_paused = False
if "is_preparing" not in st.session_state: st.session_state.is_preparing = False
if "spatial_input_df" not in st.session_state: st.session_state.spatial_input_df = None  # cache: ArcGIS-sourced PIN list, only populated once Start is pressed

# Convert area filter to acres for the (deferred) ArcGIS query
query_min_acres, query_max_acres = 0.0, 999999.0
if use_area_filter:
    if area_unit == "SqFt":
        query_min_acres = min_area_val / 43560.0
        query_max_acres = max_area_val / 43560.0
    else:
        query_min_acres = min_area_val
        query_max_acres = max_area_val

# --- Resolve data source WITHOUT ever hitting ArcGIS automatically ---
# CSV upload -> input_df is available immediately (it's the user's own bounded file, no network call).
# No CSV -> "Spatial Filter" mode: input_df stays None until the user presses Start Extraction;
# the ArcGIS county-wide query only fires inside that button's handler below.
mode = "csv" if uploaded_file is not None else "spatial"
selected_pin_col = None

if mode == "csv":
    try:
        input_df = pd.read_csv(uploaded_file, dtype=str)
    except Exception as e:
        st.error(f"Error reading uploaded CSV: {e}")
        input_df = None
    st.session_state.spatial_input_df = None  # a CSV was provided; drop any stale spatial cache
else:
    input_df = st.session_state.spatial_input_df  # None until first Start press

tab_run, tab_results = st.tabs(["🚀 Run Extraction", "📊 Results & Export"])

with tab_run:
    if mode == "csv" and input_df is not None and not input_df.empty:
        with st.container():
            st.markdown('<div class="card">', unsafe_allow_html=True)
            st.markdown('<div class="card-title">📋 Dataset Preview</div>', unsafe_allow_html=True)
            st.dataframe(input_df.head(3), use_container_width=True, height=110)
            col_names = list(input_df.columns)
            default_idx = next((i for i, c in enumerate(col_names) if any(k in c.lower() for k in ["pin", "parid", "parcel", "id"])), 0)
            selected_pin_col = st.selectbox("Select Column Representing Parcel PIN / PARID", options=col_names, index=default_idx)
            st.markdown('</div>', unsafe_allow_html=True)
    elif mode == "spatial":
        st.markdown('<div class="card">', unsafe_allow_html=True)
        st.markdown('<div class="card-title">📍 Spatial Parcel Search</div>', unsafe_allow_html=True)
        if use_area_filter:
            subtext = f"No CSV uploaded — will query ArcGIS for parcels between {min_area_val:g} {area_unit} and {max_area_val:g} {area_unit} when you press Start."
        else:
            subtext = "No Area filter set — pressing Start will pull all county parcels (can be slow). Enable the Area Filter in the sidebar to narrow this down first."
        st.markdown(f'<div class="card-subtext">{subtext}</div>', unsafe_allow_html=True)

        if input_df is not None:
            status_label = "Parcels loaded"
            status_readout = f"{len(input_df)} parcels loaded from a previous ArcGIS query. Press Start to (re)run extraction, or change filters and press Start again to re-query."
        else:
            status_label = "Ready for extraction"
            status_readout = "No parcels loaded yet — press Start / Resume Extraction below to query ArcGIS."
        st.markdown(f"""
            <div class="status-box">
                <div class="status-label">{status_label}</div>
                <div class="status-readout">{status_readout}</div>
            </div>
        """, unsafe_allow_html=True)
        st.markdown('</div>', unsafe_allow_html=True)
        selected_pin_col = "PIN"

    is_actively_running = st.session_state.is_running and not st.session_state.is_paused
    is_paused_state = st.session_state.is_paused
    is_busy = is_actively_running or st.session_state.is_preparing

    status_banner = st.empty()
    if st.session_state.is_preparing:
        status_banner.markdown('<div style="padding: 10px 14px; border-radius: 8px; background-color: #cff4fc; color: #055160; border: 1px solid #b6effb; font-weight: 600; font-size: 14px;">⏳ Preparing processing session...</div>', unsafe_allow_html=True)
    elif is_actively_running:
        status_banner.markdown('<div style="padding: 10px 14px; border-radius: 8px; background-color: #d1e7dd; color: #0f5132; border: 1px solid #badbcc; font-weight: 600; font-size: 14px;">🟢 Extraction Session is Active & Running...</div>', unsafe_allow_html=True)
    elif is_paused_state:
        status_banner.markdown('<div style="padding: 10px 14px; border-radius: 8px; background-color: #f8d7da; color: #842029; border: 1px solid #f5c2c7; font-weight: 600; font-size: 14px;">🔴 Extraction Paused / Stopped.</div>', unsafe_allow_html=True)
    # Idle state shows no banner -- the "Ready for extraction" status box above already covers it.

    st.markdown('<div class="card">', unsafe_allow_html=True)
    st.markdown('<div class="card-title">⚡ Extraction Controls</div>', unsafe_allow_html=True)
    st.markdown('<div class="card-subtext">Start a new extraction or resume a previous run.</div>', unsafe_allow_html=True)
    c1, c2, c3 = st.columns(3)
    with c1:
        st.markdown('<div class="btn-anchor btn-anchor-start"></div>', unsafe_allow_html=True)
        start_clicked = st.button("▶ Start / Resume Extraction", use_container_width=True, disabled=is_busy, key="start_btn")
    with c2:
        st.markdown('<div class="btn-anchor btn-anchor-stop"></div>', unsafe_allow_html=True)
        stop_clicked = st.button("⏸ Pause / Stop", use_container_width=True, disabled=not is_busy, key="stop_btn")
    with c3:
        st.markdown('<div class="btn-anchor btn-anchor-rerun"></div>', unsafe_allow_html=True)
        has_failed = any(r is not None and r.get("Status") != "Success" for r in st.session_state.master_results)
        rerun_failed_clicked = st.button("↻ Rerun Failed Records", use_container_width=True, disabled=is_busy or not has_failed, key="rerun_btn")
    st.markdown('</div>', unsafe_allow_html=True)

    def format_elapsed(seconds):
        if seconds is None:
            return "--:--:--"
        seconds = int(seconds)
        h, rem = divmod(seconds, 3600)
        m, s = divmod(rem, 60)
        return f"{h:02d}:{m:02d}:{s:02d}"

    def render_kpis(container, extracted, successful, failed, elapsed_str):
        container.markdown(f"""
            <div class="kpi-row">
                <div class="kpi-tile"><div class="kpi-icon blue">📋</div><div><div class="kpi-value">{extracted}</div><div class="kpi-label">Records Extracted</div><div class="kpi-sublabel">From current run</div></div></div>
                <div class="kpi-tile"><div class="kpi-icon green">✅</div><div><div class="kpi-value">{successful}</div><div class="kpi-label">Successful</div><div class="kpi-sublabel">Valid records</div></div></div>
                <div class="kpi-tile"><div class="kpi-icon orange">⚠️</div><div><div class="kpi-value">{failed}</div><div class="kpi-label">Failed</div><div class="kpi-sublabel">Needs review</div></div></div>
                <div class="kpi-tile"><div class="kpi-icon purple">🕐</div><div><div class="kpi-value">{elapsed_str}</div><div class="kpi-label">Elapsed Time</div><div class="kpi-sublabel">Current run</div></div></div>
            </div>
        """, unsafe_allow_html=True)

    kpi_placeholder = st.empty()
    _existing = [r for r in st.session_state.master_results if r is not None]
    _success_n = sum(1 for r in _existing if r.get("Status") == "Success")
    _failed_n = len(_existing) - _success_n
    render_kpis(kpi_placeholder, len(_existing), _success_n, _failed_n, format_elapsed(st.session_state.get("last_run_elapsed")))

    if stop_clicked:
        st.toast("Stopping after the current batch finishes...", icon="⏹️")
        st.session_state.is_paused = True
        st.session_state.is_running = False
        st.session_state.is_preparing = False
        st.rerun()

    if start_clicked or rerun_failed_clicked:
        st.toast("Starting extraction..." if start_clicked else "Re-running failed records...", icon="🚀")
        st.session_state.is_preparing = True
        st.session_state.is_running = False
        st.session_state.is_paused = False
        st.rerun()

    if st.session_state.is_preparing:
        st.session_state.is_preparing = False
        st.session_state.is_running = True
        st.session_state.is_paused = False

        # This is the ONLY place the county-wide ArcGIS parcel query can fire, and only because
        # the user just pressed Start/Resume/Rerun -- never on page load or an incidental rerun.
        if mode == "spatial":
            with st.spinner("🔍 Querying ArcGIS for parcels matching your Area filter..."):
                gdf = fetch_parcels_from_arcgis(query_min_acres, query_max_acres)
            if not gdf.empty and "PIN" in gdf.columns:
                st.session_state.spatial_input_df = pd.DataFrame({"PIN": gdf["PIN"].astype(str)})
                st.session_state.master_results = []  # fresh filter results -> fresh result set
            else:
                st.session_state.spatial_input_df = pd.DataFrame(columns=["PIN"])
                st.warning("No parcels matched your Area filter.")
            input_df = st.session_state.spatial_input_df
            selected_pin_col = "PIN"

        target_rows = input_df if input_df is not None else pd.DataFrame()
        if rerun_failed_clicked and len(st.session_state.master_results) > 0:
            existing_df = pd.DataFrame([r for r in st.session_state.master_results if r is not None])
            failed_pins = set(existing_df[existing_df["Status"] != "Success"]["Input_PIN"]) if not existing_df.empty else set()
            target_rows = input_df[input_df[selected_pin_col].isin(failed_pins)]
        else:
            if len(st.session_state.master_results) != len(input_df):
                st.session_state.master_results = [None] * len(input_df)

        if len(target_rows) > 0:
            st.markdown("###### 📊 Live Extraction Progress")
            progress_bar = st.progress(0)
            status_text = st.empty()
            live_preview = st.empty()

            total_records = len(input_df)
            start_time = time.time()
            last_ui_update = 0.0
            completed_count = sum(1 for r in st.session_state.master_results if r is not None)
            recent_records = []

            with ThreadPoolExecutor(max_workers=max_workers) as executor:
                futures = {executor.submit(fetch_single_parcel, idx, row[selected_pin_col], TAX_YEAR): idx for idx, row in target_rows.iterrows()}

                for future in as_completed(futures):
                    if st.session_state.is_paused: break
                    idx, record = future.result()
                    while len(st.session_state.master_results) <= idx:
                        st.session_state.master_results.append(None)
                    if st.session_state.master_results[idx] is None:
                        completed_count += 1
                    st.session_state.master_results[idx] = record
                    recent_records.append(record)
                    recent_records = recent_records[-10:]

                    now = time.time()
                    # Heartbeat: refresh the UI at least every ~10 seconds (or on every record for
                    # small/fast batches, or on the very last one) so it's always visible what the
                    # run is currently doing, instead of appearing frozen mid-batch.
                    if now - last_ui_update >= 10 or completed_count >= total_records or completed_count <= 3:
                        elapsed = now - start_time
                        st.session_state.last_run_elapsed = elapsed
                        safe_completed = min(completed_count, total_records)
                        rate = (safe_completed / elapsed) if elapsed > 0 else 0
                        remaining = total_records - safe_completed
                        eta = remaining / rate if rate > 0 else 0
                        progress_bar.progress(min(safe_completed / total_records, 1.0))
                        pct_done = (safe_completed / total_records) * 100
                        last_pin = record.get("Input_PIN", "")
                        last_status = record.get("Status", "")
                        status_text.text(f"Processed {safe_completed} of {total_records} parcels ({pct_done:.1f}% | {remaining} remaining, ~{rate:.1f}/sec, ETA {int(eta//60)}m {int(eta%60)}s) -- last: PIN {last_pin} ({last_status})")
                        live_batch = [r for r in st.session_state.master_results if r is not None]
                        live_success = sum(1 for r in live_batch if r.get("Status") == "Success")
                        render_kpis(kpi_placeholder, len(live_batch), live_success, len(live_batch) - live_success, format_elapsed(elapsed))
                        with live_preview.container():
                            st.caption("Most recently processed records:")
                            st.dataframe(pd.DataFrame(recent_records), use_container_width=True, height=180)
                        last_ui_update = now

            if not st.session_state.is_paused:
                st.session_state.is_running = False
                st.success("Extraction completed successfully! Switch to the **📊 Results & Export** tab to view/download.")
                st.rerun()

with tab_results:
    valid_master = [r for r in st.session_state.master_results if r is not None]
    if len(valid_master) > 0:
        master_df = pd.DataFrame(valid_master)

        # Apply Land Use filter robustly
        if selected_lucs:
            def match_luc(val):
                if not val: return False
                val_str = str(val).strip().upper()
                for sel in selected_lucs:
                    sel_code = sel.split(" - ")[0].strip().upper()
                    if sel_code in val_str or val_str in sel.upper(): return True
                return False
            master_df = master_df[master_df["Land_Use"].apply(match_luc)]

        st.markdown('<div class="card">', unsafe_allow_html=True)
        st.markdown("###### ✨ Master Results & Spatial Analytics")

        final_gdf = None
        if include_shapes:
            with st.spinner("Fetching parcel polygon geometries for this result set..."):
                pins_needed = master_df["Clean_PIN"].dropna().unique().tolist()
                geom_gdf, geom_errors = fetch_parcels_by_pins(pins_needed)
            if not geom_gdf.empty and "PIN" in geom_gdf.columns:
                geom_gdf["Clean_PIN"] = geom_gdf["PIN"].astype(str).str.replace(NON_DIGIT_RE, "", regex=True).str.zfill(12)
                master_df["Clean_PIN"] = master_df["Clean_PIN"].astype(str).str.zfill(12)
                final_gdf = geom_gdf.merge(master_df, on="Clean_PIN", how="inner")
                if final_gdf.crs != TARGET_CRS:
                    final_gdf = final_gdf.to_crs(TARGET_CRS)
                final_gdf = final_gdf.reset_index(drop=True)
                if final_gdf.empty:
                    st.warning(
                        f"ArcGIS returned {len(geom_gdf)} matching geometries, but none joined to "
                        f"the {len(pins_needed)} PIN(s) in this result set (Clean_PIN mismatch). "
                        "Expand the diagnostics below to inspect the raw PIN formats."
                    )
            else:
                st.markdown("""
                    <div class="info-banner">
                        Parcel geometries could not be retrieved for this result set. This may happen if the GIS service is temporarily unavailable, the request timed out, or the parcel identifiers could not be matched.
                        <div class="link-line">Extraction data and non-spatial exports are still available.</div>
                    </div>
                """, unsafe_allow_html=True)

            if geom_errors or geom_gdf.empty or (final_gdf is not None and final_gdf.empty):
                with st.expander("🔍 Geometry fetch diagnostics", expanded=True):
                    st.write(f"PINs requested: {len(pins_needed)}")
                    st.write(f"Sample requested PINs (Clean_PIN): {pins_needed[:5]}")
                    st.write(f"Sample dashed-format candidates tried: {[format_pin_dashed(p) for p in pins_needed[:5]]}")
                    st.write(f"Geometries returned by ArcGIS: {len(geom_gdf)}")
                    if not geom_gdf.empty and "PIN" in geom_gdf.columns:
                        st.write(f"Sample PIN values as stored in ArcGIS: {geom_gdf['PIN'].astype(str).head(5).tolist()}")
                    if geom_errors:
                        st.write("Errors encountered during fetch:")
                        for e in dict.fromkeys(geom_errors):  # de-duplicate, preserve order
                            st.code(e)

        if analysis_options and final_gdf is not None and not final_gdf.empty:
            analysis_status = st.empty()
            analysis_progress = st.progress(0.0)
            total_steps = len(analysis_options)
            current_step_idx = 0

            # 1. FEMA Analysis
            if "FEMA Analysis" in analysis_options:
                analysis_status.text(f"Running FEMA Flood Zone Spatial Analysis... ({current_step_idx}/{total_steps})")
                fema_gdf = fetch_arcgis_layer_to_gdf(SPATIAL_ENDPOINTS["fema"])
                st.caption(f"FEMA layer: fetched {len(fema_gdf)} feature(s).")
                if not fema_gdf.empty:
                    fema_col = next((c for c in ["FLOODZONE", "FLD_ZONE", "ZONE"] if c in fema_gdf.columns), fema_gdf.columns[0])
                    joined_fema = gpd.sjoin(final_gdf, fema_gdf[[fema_col, "geometry"]], how="left", predicate="intersects")

                    def aggregate_zones(sub_df):
                        zones = sub_df[fema_col].dropna().astype(str).unique()
                        zones = [z.strip() for z in zones if z.strip() and z.strip().lower() != "nan"]
                        return " | ".join(sorted(zones)) if zones else "None"

                    fema_summary = joined_fema.groupby(joined_fema.index).apply(aggregate_zones).reset_index(name="FEMA_Flood_Zone")
                    fema_summary.columns = ["orig_idx", "FEMA_Flood_Zone"]
                    final_gdf["FEMA_Flood_Zone"] = final_gdf.reset_index().merge(fema_summary, left_on="index", right_on="orig_idx", how="left")["FEMA_Flood_Zone"].values
                else:
                    final_gdf["FEMA_Flood_Zone"] = "Unavailable"

                current_step_idx += 1
                analysis_progress.progress(current_step_idx / total_steps)

            # 2. Sewer Analysis -- lines, and manholes, treated as fully independent layers, each
            # getting its own Intersect flag AND its own nearest-distance figure.
            if "Sewer Analysis" in analysis_options:
                analysis_status.text(f"Running Sewer Lines & Manholes Spatial Analysis... ({current_step_idx}/{total_steps})")
                sewer_line_gdfs = [fetch_arcgis_layer_to_gdf(url) for url in SPATIAL_ENDPOINTS["sewer_lines"]]
                sewer_line_gdfs = [g for g in sewer_line_gdfs if not g.empty]
                combined_sewer_lines = pd.concat(sewer_line_gdfs, ignore_index=True) if sewer_line_gdfs else gpd.GeoDataFrame(columns=["geometry"], geometry=[], crs=TARGET_CRS)

                sewer_mh_gdf = fetch_arcgis_layer_to_gdf(SPATIAL_ENDPOINTS["sewer_manholes"])
                st.caption(f"Sewer layer: fetched {len(combined_sewer_lines)} line segment(s), {len(sewer_mh_gdf)} manhole(s).")

                final_gdf["Sewer_Line_Intersect"], final_gdf["Sewer_Line_Distance_Ft"] = compute_intersect_and_distance(final_gdf, combined_sewer_lines)
                final_gdf["Sewer_Manhole_Intersect"], final_gdf["Sewer_Manhole_Distance_Ft"] = compute_intersect_and_distance(final_gdf, sewer_mh_gdf)

                current_step_idx += 1
                analysis_progress.progress(current_step_idx / total_steps)

            # 3. Water Analysis -- lines, and hydrants, same independent treatment as sewer above.
            if "Water Analysis" in analysis_options:
                analysis_status.text(f"Running Water Lines & Hydrant Spatial Analysis... ({current_step_idx}/{total_steps})")
                water_line_gdfs = [fetch_arcgis_layer_to_gdf(url) for url in SPATIAL_ENDPOINTS["water_lines"]]
                water_line_gdfs = [g for g in water_line_gdfs if not g.empty]
                combined_water_lines = pd.concat(water_line_gdfs, ignore_index=True) if water_line_gdfs else gpd.GeoDataFrame(columns=["geometry"], geometry=[], crs=TARGET_CRS)

                water_hydrant_gdf = fetch_arcgis_layer_to_gdf(SPATIAL_ENDPOINTS["water_hydrant"])
                st.caption(f"Water layer: fetched {len(combined_water_lines)} line segment(s), {len(water_hydrant_gdf)} hydrant(s).")

                final_gdf["Water_Line_Intersect"], final_gdf["Water_Line_Distance_Ft"] = compute_intersect_and_distance(final_gdf, combined_water_lines)
                final_gdf["Water_Hydrant_Intersect"], final_gdf["Water_Hydrant_Distance_Ft"] = compute_intersect_and_distance(final_gdf, water_hydrant_gdf)

                current_step_idx += 1
                analysis_progress.progress(current_step_idx / total_steps)

            analysis_status.text("✅ Spatial analysis complete!")
        elif analysis_options and (final_gdf is None or final_gdf.empty):
            st.warning("Spatial analysis modules were selected but no polygon geometry is available for this result set (check 'Include Polygon Geometries' in the sidebar).")

        display_df = pd.DataFrame(final_gdf.drop(columns="geometry")) if final_gdf is not None and "geometry" in final_gdf.columns else master_df

        # Collapse PIN / Clean_PIN / Input_PIN down to a single canonical "PIN" column for
        # display and every export format. Input_PIN is what's kept -- it's the original PIN
        # value (whatever the user supplied via CSV, or the ArcGIS-sourced PIN when running in
        # Spatial Filter mode with no CSV, which was already correct as-is). Clean_PIN is purely
        # an internal join key, and the ArcGIS "PIN" column that appears after a geometry join can
        # differ in formatting (e.g. dashed) from Input_PIN, so both are dropped in its favor.
        display_df = display_df.drop(columns=[c for c in ["PIN", "Clean_PIN"] if c in display_df.columns])
        if "Input_PIN" in display_df.columns:
            display_df = display_df.rename(columns={"Input_PIN": "PIN"})
            display_df = display_df[["PIN"] + [c for c in display_df.columns if c != "PIN"]]
        if final_gdf is not None and "geometry" in final_gdf.columns:
            final_gdf = final_gdf.drop(columns=[c for c in ["PIN", "Clean_PIN"] if c in final_gdf.columns])
            if "Input_PIN" in final_gdf.columns:
                final_gdf = final_gdf.rename(columns={"Input_PIN": "PIN"})
                final_gdf = final_gdf[["PIN"] + [c for c in final_gdf.columns if c != "PIN"]]

        show_table = st.toggle("👁️ Show Results Table / Preview", value=True)
        if show_table:
            st.dataframe(display_df, use_container_width=True)

        st.markdown("###### 📤 Download Formats")
        d1, d2, d3, d4 = st.columns(4)

        csv_data = display_df.to_csv(index=False).encode('utf-8-sig')
        with d1:
            st.download_button("📥 CSV Export", data=csv_data, file_name="lee_county_parcels.csv", mime="text/csv", type="primary", use_container_width=True)

        try:
            xlsx_buf = io.BytesIO()
            with pd.ExcelWriter(xlsx_buf, engine="openpyxl") as writer:
                display_df.to_excel(writer, index=False, sheet_name="Properties")
            xlsx_data = xlsx_buf.getvalue()
            with d2:
                st.download_button("📊 Excel Export", data=xlsx_data, file_name="lee_county_parcels.xlsx", mime="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet", type="primary", use_container_width=True)
        except Exception:
            with d2: st.button("📊 Excel Export", disabled=True, use_container_width=True)

        if final_gdf is not None and isinstance(final_gdf, gpd.GeoDataFrame) and not final_gdf.empty:
            try:
                with tempfile.TemporaryDirectory() as tmpdir:
                    gpkg_path = os.path.join(tmpdir, "lee_county_parcels.gpkg")
                    final_gdf.to_file(gpkg_path, driver="GPKG")
                    with open(gpkg_path, "rb") as f: gpkg_data = f.read()
                with d3:
                    st.download_button("🗃️ GeoPackage (.gpkg)", data=gpkg_data, file_name="lee_county_parcels.gpkg", mime="application/octet-stream", type="primary", use_container_width=True)
            except Exception:
                with d3: st.button("🗃️ GeoPackage", disabled=True, use_container_width=True)
        else:
            with d3: st.button("🗃️ GeoPackage", disabled=True, use_container_width=True)

        if final_gdf is not None and isinstance(final_gdf, gpd.GeoDataFrame) and not final_gdf.empty:
            try:
                with tempfile.TemporaryDirectory() as tmpdir:
                    shp_path = os.path.join(tmpdir, "lee_county_parcels.shp")
                    final_gdf.to_file(shp_path, driver="ESRI Shapefile")
                    zip_path = os.path.join(tmpdir, "shapefile.zip")
                    with zipfile.ZipFile(zip_path, 'w') as zipf:
                        for root, _, files in os.walk(tmpdir):
                            for file in files:
                                if file.endswith((".shp", ".shx", ".dbf", ".prj", ".cpg")):
                                    zipf.write(os.path.join(root, file), arcname=file)
                    with open(zip_path, "rb") as f: shp_zip_data = f.read()
                with d4:
                    st.download_button("🗺️ Shapefile (.zip)", data=shp_zip_data, file_name="lee_county_parcels_shp.zip", mime="application/zip", type="primary", use_container_width=True)
            except Exception:
                with d4: st.button("🗺️ Shapefile (.zip)", disabled=True, use_container_width=True)
        else:
            with d4: st.button("🗺️ Shapefile (.zip)", disabled=True, use_container_width=True)

        st.markdown('</div>', unsafe_allow_html=True)
    else:
        st.info("No results yet -- head to the **🚀 Run Extraction** tab and press Start.")
