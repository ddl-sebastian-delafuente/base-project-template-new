import nypd
import pandas as pd
import numpy as np
from datetime import datetime, date, timedelta
from dateutil import relativedelta
from dateutil.relativedelta import relativedelta
import base64
import PIL
from PIL import Image, ImageFont, ImageDraw, ImageEnhance
from io import BytesIO
import datetime as dt
import hashlib
import os
import re

import urllib3
import xml.etree.ElementTree as ET

import requests
import ssl

from email.message import EmailMessage
import mimetypes
import smtplib

import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
import matplotlib.lines as mlines

import geopandas as gpd
from fiona.crs import from_epsg  # this method is depricated

# from pyproj import CRS # use this calss to initiate CRS
from shapely.geometry import Point
import pyproj
from shapely.ops import transform


from typing import Any

urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)
ssl._create_default_https_context = ssl._create_unverified_context


today = datetime.today()


def divide_long_list_into_chunks(l, chunk_size=10000):
    def generate_chunks(l, chunk_size):
        for i in range(0, len(l), chunk_size):
            yield l[i : i + chunk_size]

    return list(generate_chunks(l, chunk_size))


def get_GRIP_Shootings_Shots_Fired_Stats(predefined_date):
    """User input a predefined date (the date has to be greater than 1/1/2018) for the shootings/shots fired incidents start date
    for the statistic.
    The function generates statistic for the following:
    1. Percentage of the GRIP subjects were involved in percentage of the shootings
       along with the open/open felony cases statistic
    2. Percentage of the GRIP subjects were responsible for percentage of the shootings
       along with the open/open felony cases statistic
    3. Percentage of the GRIP subjects were involved in percentage of the shootings and
       shots fired along with the open/open felony cases statistic
    4. Percentage of the GRIP subjects were responsible for percentage of the shootings
       and shots fired along with the open/open felony cases statistic"""

    today = dt.date.today()
    End_Date = today + dt.timedelta(days=-1)
    Start_Date = dt.date(2021, 1, 1)
    Start_Date_2020 = dt.date(2020, 1, 1)
    rolling_year_start_date = dt.date(2018, 1, 1)

    # Pull NYSIDs for homicide victims

    Homicide_NYSID_SQL = nypd.get_data(
        """SELECT DISTINCT NYSID_NUM
                                           FROM CID.VIC_VICTIM VIC
                                           JOIN CID.PSN_PERSON_OCCUR PSN
                                           ON VIC.EVNT_KEY = PSN.EVNT_KEY 
                                           AND VIC.PRSN_ROLE_SEQ_NUM = PSN.PRSN_ROLE_SEQ_NUM
                                           AND VIC.EVNT_TYP_CD = PSN.EVNT_TYP_CD
                                           AND VIC.ROLE_CD = PSN.ROLE_CD
                                           AND VIC.VIC_DEAD_FLG = 'Y'
                                           WHERE NYSID_NUM IS NOT NULL AND  NYSID_NUM!= 'NONE' AND PSN.ROW_INSERT_DT>='2019-01-01'"""
    )

    homicide_nysid = nypd.clean_data(Homicide_NYSID_SQL)
    homicide_nysid_list = list(homicide_nysid.nysid_num)

    ### Pull Population NYSIDs for shootings since the start date

    Shooting_NYSID_SQL = nypd.get_data(
        """ SELECT DISTINCT NYSID_NUM
                                        FROM
                                        (
                                        SELECT DISTINCT NYSID_NUM
                                        FROM CID.SHI_SH_INCIDENT SHT
                                        JOIN CID.PSN_PERSON_OCCUR PSN
                                        ON SHT.SHT_HMCD_INCDT_KEY = PSN.EVNT_KEY
                                        WHERE SHT.CASE_STAT_CD NOT IN ('6', '8') AND
                                              SHT.PCT_CD in (1,5,6,7,9,10,13,14,17,18,19,20,22,23,24,25,26,28,30,32,33,34,40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 52,
                                                                  60, 61, 62, 63, 66, 67, 68, 69, 70, 71, 72, 76, 78,
                                                                  73, 75, 77, 79, 81, 83, 84, 88, 90, 94,
                                                                  100, 101, 102, 103, 105, 106, 107, 113,
                                                                  104, 108, 109, 110, 111, 112, 114, 115,
                                                                  120, 121, 122, 123) AND METHD_USE_DESC = 'SHOT' AND SHTING_CLASS_CD in ('1', '2') AND {date_filter} 
                                                                  AND NYSID_NUM IS NOT NULL
                                        UNION
                                        SELECT DISTINCT NYSID_NUM
                                                FROM CID.ARR_ARREST ARR
                                                JOIN CID.CAA_CMPT_ARST_ASOC ARR_ASOC
                                                ON ARR.ARR_KEY = ARR_ASOC.ARR_KEY AND ARR_VOIDED_FLG = 'N'
                                                JOIN CID.CSA_CMPT_SHI_ASOC C
                                                ON C.CMPLNT_KEY = ARR_ASOC.CMPLNT_KEY
                                                JOIN CID.SHI_SH_INCIDENT SHT
                                                ON SHT.SHT_HMCD_INCDT_KEY = C.SHT_HMCD_INCDT_KEY
                                        WHERE SHT.CASE_STAT_CD NOT IN ('6', '8') AND
                                              SHT.PCT_CD in (1,5,6,7,9,10,13,14,17,18,19,20,22,23,24,25,26,28,30,32,33,34,40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 52,
                                                                  60, 61, 62, 63, 66, 67, 68, 69, 70, 71, 72, 76, 78,
                                                                  73, 75, 77, 79, 81, 83, 84, 88, 90, 94,
                                                                  100, 101, 102, 103, 105, 106, 107, 113,
                                                                  104, 108, 109, 110, 111, 112, 114, 115,
                                                                  120, 121, 122, 123) AND METHD_USE_DESC = 'SHOT' AND SHTING_CLASS_CD in ('1', '2') AND {date_filter} 
                                                                  AND NYSID_NUM IS NOT NULL AND C.CMPLNT_KEY!=0
                                        UNION
                                        SELECT DISTINCT SBJ_NYSID AS NYSID_NUM
                                        FROM CID.SHI_SH_INCIDENT SHT
                                        JOIN CID.CSA_CMPT_SHI_ASOC C
                                        ON C.SHT_HMCD_INCDT_KEY = SHT.SHT_HMCD_INCDT_KEY
                                        JOIN STAGE.ICARDS Icard
                                        ON Icard.CMPLNT_KEY = C.CMPLNT_KEY AND REC_CNL_DT IS NULL
                                        WHERE SHT.CASE_STAT_CD NOT IN ('6', '8') AND
                                              SHT.PCT_CD in (1,5,6,7,9,10,13,14,17,18,19,20,22,23,24,25,26,28,30,32,33,34,40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 52,
                                                                  60, 61, 62, 63, 66, 67, 68, 69, 70, 71, 72, 76, 78,
                                                                  73, 75, 77, 79, 81, 83, 84, 88, 90, 94,
                                                                  100, 101, 102, 103, 105, 106, 107, 113,
                                                                  104, 108, 109, 110, 111, 112, 114, 115,
                                                                  120, 121, 122, 123) AND METHD_USE_DESC = 'SHOT' AND SHTING_CLASS_CD in ('1', '2') AND {date_filter} 
                                                                  AND SBJ_NYSID IS NOT NULL
                                        )""".format(
            date_filter="OCCUR_DT BETWEEN '{:%Y-%m-%d}' AND '{:%Y-%m-%d}'".format(
                Start_Date, End_Date
            )
        )
    )

    shootings_nysid = nypd.clean_data(Shooting_NYSID_SQL)

    ### Pull Population NYSIDs for shots fired since the start date
    def shotsfired_complaints(start_dt, end_dt):
        """
        Below query pulls shots-fired complaints that meet the following criteria
        1) Classified as "investigate shots fired", "reckless endangerment", or "attempted assault" in a complaint
        2) Ballistics vouchered in PETS under the category of "firearm"
        3) PETS narrative contains certain keywords, such as "SHOT", "BULLET", "SHELL CASING", "FIRE", and "ROUNDs"
        4) Excluded unfounded or voided complaints
        """

        shotsfired_sql = f"""
        SELECT DISTINCT
	        CMPLNT.CMPLNT_KEY,
	        CMPLNT.CMPLNT_ID,
	        CMPLNT.CMPLNT_FR_DT,
	        CMPLNT.CMPLNT_FR_TM,
	        CMPLNT.RPT_DT,
	        CMPLNT.CMPLNT_PCT_CD,
	        PSB.PATRL_BORO_CD,
	        CMPLNT.RPT_CLASSFCTN_DESC,
	        PKC.PD_DESC as PKC_PD_DESC,
	        CMPLNT.CRM_ATPT_CPTD_CD,
	        PKC.OFNS_DESC,
	        CMPLNT.PD_CD,
	        CMPLNT.CLEAR_CD,
	        COD.LIT_LONG_DESC as CLEAR_DESC,
	        ADDR.FULL_ADDR_DESC,
	        ADDR.X_COORD_CD,
	        ADDR.Y_COORD_CD,
	        ADDR.ORIG_X_COORD_CD,
	        ADDR.ORIG_Y_COORD_CD,
	        ADDR.BEST_SCORE_REQUEST,
	        PET_PETS_INVOICE.EVNT_KEY as EVNT_KEY, 
	        PET_PETS_INVOICE.INVOICE_NUM as INVOICE_NUM, 
	        PET_PETS_INVOICE.PRPRTY_CAT_CD as PRPRTY_CAT_CD, 
	        PET_PETS_INVOICE.PRPRTY_TYP_CD as PRPRTY_TYP_CD, 
	        PET_PETS_INVOICE.CREATE_DT as CREATE_DT, 
	        PET_PETS_INVOICE.INV_STATUS_DESC as INV_STATUS_DESC, 
	        PET_PROPERTY.PRODUCT_HIERARCHY_CD,
	        CAT.PRPRTY_CAT_DESC,
	        MAT.DESCRIPTION
	 
	    FROM 
	        CID.CVR_CMPLNT_VERSION CMPLNT
	        
	    LEFT JOIN
	        CID.PSB_PUB_SERV_GEO PSB
	        ON PSB.PSB_GEO_KEY = CMPLNT.PSB_GEO_KEY
	    
	    LEFT JOIN CID.PET_PETS_INVOICE PET_PETS_INVOICE
	        ON CMPLNT.CMPLNT_ID =PET_PETS_INVOICE.CMPLNT_ID
	    LEFT JOIN CID.PKC_PD_KEY_CODE PKC
	        ON CMPLNT.PD_CD = PKC.PD_CD  
	 
	    LEFT JOIN CID.PEP_PETS_PROPERTY PET_PROPERTY
	        ON PET_PROPERTY.EVNT_KEY = PET_PETS_INVOICE.EVNT_KEY
	        AND PET_PROPERTY.INVOICE_NUM = PET_PETS_INVOICE.INVOICE_NUM
	 
	    LEFT OUTER JOIN CID.PETS_PRPRTY_CATEGORY CAT
	        ON PET_PETS_INVOICE.PRPRTY_CAT_CD = CAT.PRPRTY_CAT_CD
	 
	    LEFT OUTER JOIN CID.PETS_PRPRTY_TYPE TYP
	        ON PET_PROPERTY.PRPRTY_TYP_CD = TYP.PRPRTY_TYP_CD
	        AND PET_PROPERTY.PRODUCT_HIERARCHY_CD = TYP.PRODUCT_HIERARCHY_CD
	 
	    LEFT OUTER JOIN CID.PETS_MATERIAL_TYPE MAT
	        ON PET_PROPERTY.MATERIAL_NUM = MAT.MATERIAL_NO
	 
	    LEFT JOIN CID.NAR_NARRTV NAR
	        ON NAR.EVNT_KEY=PET_PETS_INVOICE.CMPLNT_KEY
	        AND NAR.NARRTV_TYP_CD = 'C'
	    
	    LEFT JOIN CID.ADR_ADDRESS_OCCUR ADDR
	        ON CMPLNT.CMPLNT_KEY = ADDR.EVNT_KEY
	        AND ADDR.EVNT_TYP_CD='C'
	        AND ADDR.ADDR_TYP_CD='C'
	    
	    LEFT JOIN CID.COD_CODES_ALL COD
	        ON CMPLNT.CLEAR_CD = COD.CD_VAL
	        AND COD.TABLE_NUM = 872
	 
	    WHERE
	        (((PET_PETS_INVOICE.INV_STATUS_DESC NOT LIKE '%HIGH PROFILE%' OR PET_PETS_INVOICE.INV_STATUS_DESC IS NULL)
	        AND TYP.PRPRTY_TYP_DESC IN ('FIREARM')
	        AND ((NAR.EVNT_NARRTV_DESC like '%SHOT%' or
	 
	            NAR.EVNT_NARRTV_DESC like '%BULLET%' or
	            NAR.EVNT_NARRTV_DESC like '%SHELL CASING%' or
	            NAR.EVNT_NARRTV_DESC like '%SHELLCASING%' or
	            (NAR.EVNT_NARRTV_DESC like '%DISCHARGE%' AND NAR.EVNT_NARRTV_DESC like '%FIREARM%') or
	            (NAR.EVNT_NARRTV_DESC like '%DISCHARGE%' AND NAR.EVNT_NARRTV_DESC like '%HANDGUN%') or
	            (NAR.EVNT_NARRTV_DESC like '%FIRE%' AND NAR.EVNT_NARRTV_DESC like '%ROUND%') OR
	            (NAR.EVNT_NARRTV_DESC like '%FIRI%' AND NAR.EVNT_NARRTV_DESC like '%ROUND%') OR
	            (NAR.EVNT_NARRTV_DESC like '%FIRI%' AND NAR.EVNT_NARRTV_DESC like '%HANDGUN%') OR
	            (NAR.EVNT_NARRTV_DESC like '%FIRE%' AND NAR.EVNT_NARRTV_DESC like '%HANDGUN%') OR
	            (NAR.EVNT_NARRTV_DESC like '%SPENT%' AND NAR.EVNT_NARRTV_DESC like '%ROUND%') OR
	            (NAR.EVNT_NARRTV_DESC like '%FIRED%') OR
	            (NAR.EVNT_NARRTV_DESC like '%BALLISTIC%') OR
	            (NAR.EVNT_NARRTV_DESC like '%SHOOTING%' AND NAR.EVNT_NARRTV_DESC like '%ROUNDS%') OR
	            (NAR.EVNT_NARRTV_DESC like '%DISCHARGING%' AND NAR.EVNT_NARRTV_DESC like '%FIREARM%')
	            )
	 
	        AND (NAR.EVNT_NARRTV_DESC not like '%BB GUN%'))
	        AND TYP.PRODUCT_HIERARCHY_DESC in ('AMMUNITION','HANDGUN','LONG GUN','PART & ACCESSORY')
	        AND CMPLNT.PD_CD in ('117', '083', '109', '277')
	        )
	        OR CMPLNT.PD_CD in ('804', '088', '089'))
	        AND (CMPLNT.CLEAR_CD <> '1' OR CMPLNT.CLEAR_CD IS NULL)
	        AND (CMPLNT.CMPLNT_FR_DT>='{start_dt}' AND CMPLNT.CMPLNT_FR_DT<='{end_dt}')
	                                     
        """

        df = nypd.get_data(shotsfired_sql, clean=False)
        df = nypd.clean_data(
            df, clean_strings="auto", to_datetime="auto", clean_nysids=False
        )

        df["cmplnt_fr_dt"] = pd.to_datetime(df["cmplnt_fr_dt"])
        df["cmplnt_fr_tm"] = pd.to_timedelta(df["cmplnt_fr_tm"])
        df["cmplnt_fr_dt_tm"] = df["cmplnt_fr_dt"] + df["cmplnt_fr_tm"]

        df["new_ofns_desc"] = np.where(
            df["pkc_pd_desc"].str.contains("SHOTS FI"), "SHOTS FIRED", df["ofns_desc"]
        )
        df["new_ofns_desc"] = np.where(
            df["pkc_pd_desc"].str.contains("RECKLESS"),
            "SHOTS FIRED",
            df["new_ofns_desc"],
        )
        df["new_ofns_desc"] = np.where(
            (
                (df["new_ofns_desc"].str.contains("ASSAULT"))
                & (df["crm_atpt_cptd_cd"] == "ATTEMPTED")
            ),
            "SHOTS FIRED",
            df["new_ofns_desc"],
        )
        df["new_ofns_desc"] = np.where(
            df["pkc_pd_desc"].str.contains("GUNSHT DET"),
            "SHOTS FIRED",
            df["new_ofns_desc"],
        )

        df = df[df["new_ofns_desc"].isin(["SHOTS FIRED"])]

        return df

    shotsfired_complaints_list = shotsfired_complaints(
        Start_Date.strftime("%Y-%m-%d"), End_Date.strftime("%Y-%m-%d")
    )

    original_complaint_id_list = list(shotsfired_complaints_list["cmplnt_id"])
    for i in ["202106000570899", "202107900587199"]:
        original_complaint_id_list.append(i)
    shotsfired_complaints_id_list = tuple(set(original_complaint_id_list))

    original_complaint_key_list = list(shotsfired_complaints_list["cmplnt_key"])
    for i in [234603198, 233168319]:
        original_complaint_key_list.append(i)
    shotsfired_complaints_key_list = tuple(set(original_complaint_key_list))

    # get nysid who were involved in shots fired

    shotsfired_psn_sql = f"""
	                         SELECT DISTINCT NYSID_NUM
	                         FROM CID.PSN_PERSON_OCCUR
	                         WHERE EVNT_ID IN {shotsfired_complaints_id_list} AND NYSID_NUM IS NOT NULL"""

    shotsfired_psn_nysid = nypd.get_data(shotsfired_psn_sql)
    shotsfired_psn_nysid = nypd.clean_data(shotsfired_psn_nysid)

    # get nysid who were involved in shots fired has icard

    shotsfired_icard_sql = f""" SELECT DISTINCT SBJ_NYSID NYSID_NUM
	                             FROM STAGE.ICARDS
	                             WHERE REC_CNL_DT IS NULL AND SBJ_NYSID IS NOT NULL
	                                   AND CMPLNT_KEY IN {shotsfired_complaints_key_list}"""

    shotsfired_icard_nysid = nypd.get_data(shotsfired_icard_sql)
    shotsfired_icard_nysid = nypd.clean_data(shotsfired_icard_nysid)

    # get nysid who were involved in shots fired with arrest

    shotsfired_arrest_sql = f""" SELECT DISTINCT NYSID_NUM
	                              FROM CID.ARR_ARREST ARR
	                              JOIN CID.CAA_CMPT_ARST_ASOC ARR_ASOC
	                              ON ARR.ARR_KEY = ARR_ASOC.ARR_KEY AND ARR_VOIDED_FLG = 'N'
	                              WHERE CMPLNT_ID IN {shotsfired_complaints_id_list} AND NYSID_NUM IS NOT NULL"""

    shotsfired_arrest_nysid = nypd.get_data(shotsfired_arrest_sql)
    shotsfired_arrest_nysid = nypd.clean_data(shotsfired_arrest_nysid)

    # combine shootins/shots fired NYSID (NYISD for shootings/shots fired)

    nysid_list = tuple(
        set(
            list(shootings_nysid["nysid_num"])
            + list(shotsfired_psn_nysid["nysid_num"])
            + list(shotsfired_icard_nysid["nysid_num"])
            + list(shotsfired_arrest_nysid["nysid_num"])
        )
    )

    nysid_list = tuple(
        set([x for x in list(nysid_list) if x not in homicide_nysid_list])
    )

    Shooting_Record_SQL = nypd.get_data(
        """ SELECT DISTINCT NYSID_NUM,
	                                                         SHT_HMCDE_INCDT_ID ID,
	                                                         OCCUR_DT,
	                                                         OCCUR_TM,
	                                                         PCT,
	                                                         FATAL,
	                                                         ROLE_DESC,
	                                                         SGHT_AS_DESC,
	                                                         'SHOOTING' AS TYPE,
	                                                         CMPLNT_ID
	        
	                                        FROM
	                                        (
	                                        SELECT DISTINCT NYSID_NUM,
	                                                        SHT.SHT_HMCDE_INCDT_ID,
	                                                         OCCUR_DT,
	                                                         OCCUR_TM,
	                                                         PCT_CD PCT,
	                                                         CASE
	                                                               WHEN SHTING_CLASS_CD = '1' THEN 'FATAL'
	                                                               WHEN SHTING_CLASS_CD = '2' THEN 'NON-FATAL'
	                                                         END AS FATAL,
	                                                         ROLE_DESC,
	                                                         '' SGHT_AS_DESC,
	                                                         YEAR(OCCUR_DT) || '-' || PCT_CD ||  '-' || TRIM(LEADING '0' FROM SHT.CMPLNT_NUM) CMPLNT_ID

	                                        FROM CID.SHI_SH_INCIDENT SHT
	                                        JOIN CID.PSN_PERSON_OCCUR PSN
	                                        ON SHT.SHT_HMCD_INCDT_KEY = PSN.EVNT_KEY
	                                        LEFT JOIN CID.ROL_ROLE_CODE role_code
	                                        ON role_code.ROLE_CD = PSN.ROLE_CD
	                                        WHERE SHT.CASE_STAT_CD NOT IN ('6', '8') AND
	                                              SHT.PCT_CD in (1,5,6,7,9,10,13,14,17,18,19,20,22,23,24,25,26,28,30,32,33,34,40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 52,
	                                                                  60, 61, 62, 63, 66, 67, 68, 69, 70, 71, 72, 76, 78,
	                                                                  73, 75, 77, 79, 81, 83, 84, 88, 90, 94,
	                                                                  100, 101, 102, 103, 105, 106, 107, 113,
	                                                                  104, 108, 109, 110, 111, 112, 114, 115,
	                                                                  120, 121, 122, 123) AND METHD_USE_DESC = 'SHOT' AND SHTING_CLASS_CD in ('1', '2') AND {date_filter} 
	                                                                  AND NYSID_NUM IS NOT NULL
	                                        UNION
	                                        SELECT DISTINCT NYSID_NUM,
	                                                        SHT.SHT_HMCDE_INCDT_ID,
	                                                        OCCUR_DT,
	                                                        OCCUR_TM,
	                                                        PCT_CD PCT,
	                                                        CASE
	                                                               WHEN SHTING_CLASS_CD = '1' THEN 'FATAL'
	                                                               WHEN SHTING_CLASS_CD = '2' THEN 'NON-FATAL'
	                                                        END AS FATAL,
	                                                        'Arrest' ROLE_DESC,
	                                                        '' SGHT_AS_DESC,
	                                                        YEAR(OCCUR_DT) || '-' || PCT_CD ||  '-' || TRIM(LEADING '0' FROM SHT.CMPLNT_NUM) CMPLNT_ID
	                                                FROM CID.ARR_ARREST ARR
	                                                JOIN CID.CAA_CMPT_ARST_ASOC ARR_ASOC
	                                                ON ARR.ARR_KEY = ARR_ASOC.ARR_KEY AND ARR_VOIDED_FLG = 'N'
	                                                JOIN CID.CSA_CMPT_SHI_ASOC C
	                                                ON C.CMPLNT_KEY = ARR_ASOC.CMPLNT_KEY
	                                                JOIN CID.SHI_SH_INCIDENT SHT
	                                                ON SHT.SHT_HMCD_INCDT_KEY = C.SHT_HMCD_INCDT_KEY AND C.CMPLNT_KEY!=0
	                                        WHERE SHT.CASE_STAT_CD NOT IN ('6', '8') AND
	                                              SHT.PCT_CD in (1,5,6,7,9,10,13,14,17,18,19,20,22,23,24,25,26,28,30,32,33,34,40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 52,
	                                                                  60, 61, 62, 63, 66, 67, 68, 69, 70, 71, 72, 76, 78,
	                                                                  73, 75, 77, 79, 81, 83, 84, 88, 90, 94,
	                                                                  100, 101, 102, 103, 105, 106, 107, 113,
	                                                                  104, 108, 109, 110, 111, 112, 114, 115,
	                                                                  120, 121, 122, 123) AND METHD_USE_DESC = 'SHOT' AND SHTING_CLASS_CD in ('1', '2') AND {date_filter} 
	                                                                  AND NYSID_NUM IS NOT NULL
	                                        UNION
	                                        SELECT DISTINCT SBJ_NYSID AS NYSID_NUM, 
	                                                        SHT.SHT_HMCDE_INCDT_ID,
	                                                        OCCUR_DT,
	                                                        OCCUR_TM,
	                                                        PCT_CD PCT,
	                                                        CASE
	                                                               WHEN SHTING_CLASS_CD = '1' THEN 'FATAL'
	                                                               WHEN SHTING_CLASS_CD = '2' THEN 'NON-FATAL'
	                                                         END AS FATAL,
	                                                         '' ROLE_DESC,
	                                                         SGHT_AS_DESC,
	                                                         YEAR(OCCUR_DT) || '-' || PCT_CD ||  '-' || TRIM(LEADING '0' FROM SHT.CMPLNT_NUM) CMPLNT_ID
	                                              
	                                        FROM CID.SHI_SH_INCIDENT SHT
	                                        JOIN CID.CSA_CMPT_SHI_ASOC C
	                                        ON C.SHT_HMCD_INCDT_KEY = SHT.SHT_HMCD_INCDT_KEY
	                                        JOIN STAGE.ICARDS Icard
	                                        ON Icard.CMPLNT_KEY = C.CMPLNT_KEY AND REC_CNL_DT IS NULL
	                                        WHERE SHT.CASE_STAT_CD NOT IN ('6', '8') AND
	                                              SHT.PCT_CD in (1,5,6,7,9,10,13,14,17,18,19,20,22,23,24,25,26,28,30,32,33,34,40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 52,
	                                                                  60, 61, 62, 63, 66, 67, 68, 69, 70, 71, 72, 76, 78,
	                                                                  73, 75, 77, 79, 81, 83, 84, 88, 90, 94,
	                                                                  100, 101, 102, 103, 105, 106, 107, 113,
	                                                                  104, 108, 109, 110, 111, 112, 114, 115,
	                                                                  120, 121, 122, 123) AND METHD_USE_DESC = 'SHOT' AND SHTING_CLASS_CD in ('1', '2') AND {date_filter} 
	                                                                  AND SBJ_NYSID IS NOT NULL
	                                        )""".format(
            date_filter="OCCUR_DT BETWEEN '{:%Y-%m-%d}' AND '{:%Y-%m-%d}'".format(
                rolling_year_start_date, End_Date
            )
        )
    )

    hist_shootings_Record = nypd.clean_data(
        Shooting_Record_SQL, to_datetime=[{"occur_datetime": ["occur_dt", "occur_tm"]}]
    )
    hist_shootings_Record = hist_shootings_Record[
        hist_shootings_Record["nysid_num"].isin(list(nysid_list))
    ]

    # pull shots fired for the 3 rolling years
    hist_shotsfired_record = shotsfired_complaints(
        rolling_year_start_date.strftime("%Y-%m-%d"), End_Date.strftime("%Y-%m-%d")
    )

    original_complaint_id_list = list(hist_shotsfired_record["cmplnt_id"])
    for i in ["202106000570899", "202107900587199"]:
        original_complaint_id_list.append(i)
    hist_shotsfired_record_id_list = tuple(set(original_complaint_id_list))

    original_complaint_key_list = list(hist_shotsfired_record["cmplnt_key"])
    for i in [234603198, 233168319]:
        original_complaint_key_list.append(i)
    hist_shotsfired_record_key_list = tuple(set(original_complaint_key_list))

    hist_shotsfired_psn_sql = f"""
	                         SELECT DISTINCT NYSID_NUM,
	                                         EVNT_ID ID,
	                                         CMPLNT_FR_DT OCCUR_DT,
	                                         CMPLNT_FR_TM OCCUR_TM,
	                                         CMPLNT_PCT_CD PCT,
	                                         '' FATAL,
	                                         ROLE_DESC,
	                                         NULL SGHT_AS_DESC, 
	                                         'SHOTS FIRED' TYPE,
	                                         LEFT(C.CMPLNT_ID, 4) || '-' || RIGHT(LEFT(C.CMPLNT_ID, 7), 3) || '-' || TRIM(LEADING '0' FROM RIGHT(LEFT(C.CMPLNT_ID, 13),6)) CMPLNT_ID
	                         FROM CID.PSN_PERSON_OCCUR PSN
	                         JOIN CID.CVR_CMPLNT_VERSION C
	                         ON PSN.EVNT_KEY =  C.CMPLNT_KEY
	                         LEFT JOIN CID.ROL_ROLE_CODE role_code
	                         ON role_code.ROLE_CD = PSN.ROLE_CD
	                         WHERE EVNT_ID IN {hist_shotsfired_record_id_list} AND NYSID_NUM IS NOT NULL"""

    hist_shotsfired_psn_nysid = nypd.get_data(hist_shotsfired_psn_sql)
    hist_shotsfired_psn_record = nypd.clean_data(
        hist_shotsfired_psn_nysid,
        to_datetime=[{"occur_datetime": ["occur_dt", "occur_tm"]}],
    )
    hist_shotsfired_psn_record = hist_shotsfired_psn_record[
        hist_shotsfired_psn_record["nysid_num"].isin(list(nysid_list))
    ]

    hist_shotsfired_icard_sql = f""" SELECT DISTINCT SBJ_NYSID NYSID_NUM,
	                                                    CMPLNT_ID ID,
	                                                    CMPLNT_FR_DT OCCUR_DT,
	                                                    CMPLNT_FR_TM OCCUR_TM,
	                                                    CMPLNT_PCT_CD PCT,
	                                                    '' FATAL,
	                                                    NULL ROLE_DESC,
	                                                    SGHT_AS_DESC,
	                                                    'SHOTS FIRED' TYPE,
	                                                    LEFT(C.CMPLNT_ID, 4) || '-' || RIGHT(LEFT(C.CMPLNT_ID, 7), 3) || '-' || TRIM(LEADING '0' FROM RIGHT(LEFT(C.CMPLNT_ID, 13),6)) CMPLNT_ID
	                                    FROM STAGE.ICARDS Icard
	                                    JOIN CID.CVR_CMPLNT_VERSION C
	                                    ON Icard.CMPLNT_KEY = C.CMPLNT_KEY
	                                    WHERE REC_CNL_DT IS NULL
	                                          AND Icard.CMPLNT_KEY IN {hist_shotsfired_record_key_list} AND SBJ_NYSID IS NOT NULL"""

    hist_shotsfired_icard_nysid = nypd.get_data(hist_shotsfired_icard_sql)
    hist_shotsfired_icard_record = nypd.clean_data(
        hist_shotsfired_icard_nysid,
        to_datetime=[{"occur_datetime": ["occur_dt", "occur_tm"]}],
    )
    hist_shotsfired_icard_record = hist_shotsfired_icard_record[
        hist_shotsfired_icard_record["nysid_num"].isin(list(nysid_list))
    ]

    hist_shotsfired_arrest_sql = f""" SELECT DISTINCT NYSID_NUM,
	                                                     C.CMPLNT_ID ID,
	                                                     CMPLNT_FR_DT OCCUR_DT,
	                                                     CMPLNT_FR_TM OCCUR_TM,
	                                                     CMPLNT_PCT_CD PCT,
	                                                     '' FATAL,
	                                                      'Arrest' ROLE_DESC,
	                                                     NULL SGHT_AS_DESC,
	                                                     'SHOTS FIRED' TYPE,
	                                                     LEFT(C.CMPLNT_ID, 4) || '-' || RIGHT(LEFT(C.CMPLNT_ID, 7), 3) || '-' || TRIM(LEADING '0' FROM RIGHT(LEFT(C.CMPLNT_ID, 13),6)) CMPLNT_ID
	                                     FROM CID.ARR_ARREST ARR
	                                     JOIN CID.CAA_CMPT_ARST_ASOC ARR_ASOC
	                                     ON ARR.ARR_KEY = ARR_ASOC.ARR_KEY AND ARR_VOIDED_FLG = 'N'
	                                     JOIN CID.CVR_CMPLNT_VERSION C
	                                     ON ARR_ASOC.CMPLNT_KEY = C.CMPLNT_KEY
	                                     WHERE C.CMPLNT_ID IN {hist_shotsfired_record_id_list} AND NYSID_NUM IS NOT NULL"""

    hist_shotsfired_arrest_nysid = nypd.get_data(hist_shotsfired_arrest_sql)
    hist_shotsfired_arrest_record = nypd.clean_data(
        hist_shotsfired_arrest_nysid,
        to_datetime=[{"occur_datetime": ["occur_dt", "occur_tm"]}],
    )
    hist_shotsfired_arrest_record = hist_shotsfired_arrest_record[
        hist_shotsfired_arrest_record["nysid_num"].isin(list(nysid_list))
    ]

    hist_record = pd.concat(
        [
            hist_shootings_Record,
            hist_shotsfired_psn_record,
            hist_shotsfired_icard_record,
            hist_shotsfired_arrest_record,
        ]
    )
    hist_record = hist_record[~hist_record.nysid_num.isin(["09999999J", "00000000H"])]

    hist_record = hist_record.reset_index(drop=True)

    hist_record.loc[hist_record["role_desc"].isna(), "role_desc"] = hist_record[
        "sght_as_desc"
    ]

    hist_record.loc[hist_record.role_desc.isna(), "role_desc"] = ""
    hist_record.loc[hist_record.sght_as_desc.isna(), "sght_as_desc"] = ""
    hist_record.loc[hist_record.fatal.isna(), "fatal"] = ""

    hist_record.loc[
        hist_record["role_desc"] == "PERPETRATOR - PROBABLE CAUSE TO ARREST",
        "role_desc",
    ] = "PC Icard"
    hist_record.loc[hist_record["role_desc"] == "Person Of Interest", "role_desc"] = (
        "POI"
    )
    hist_record.loc[
        hist_record["role_desc"] == "SUSPECT ONLY - NO PROBABLE CAUSE TO ARREST",
        "role_desc",
    ] = "Suspect"

    hist_record_duplicates = hist_record.drop_duplicates()
    hist_record_role_concat = (
        hist_record_duplicates.groupby(
            [
                "nysid_num",
                "id",
                "occur_dt",
                "occur_tm",
                "pct",
                "fatal",
                "type",
                "cmplnt_id",
            ]
        )["role_desc"]
        .apply(lambda x: ", ".join(x))
        .reset_index()
    )

    # cleaning up duplicates
    shooting_complaints_df = nypd.get_data(
        f""" SELECT DISTINCT SHT_HMCDE_INCDT_ID,
	                                                   LEFT(CMPLNT_ID, 4) || '-' || RIGHT(LEFT(CMPLNT_ID, 7), 3) || '-' || TRIM(LEADING '0' FROM RIGHT(LEFT(CMPLNT_ID, 13),6)) CMPLNT_ID,
	                                                   CMPLNT_ID ORIG_CMPLNT_ID
	                                            FROM CID.CSA_CMPT_SHI_ASOC

	                                          WHERE CMPLNT_KEY!=0 AND 
	                                                 SHT_HMCDE_INCDT_ID IN {tuple(set(hist_record_role_concat[hist_record_role_concat['type']=='SHOOTING']['id']))}"""
    )

    shooting_complaints_df = nypd.clean_data(shooting_complaints_df)

    shooting_sf_complaint_match_df = pd.merge(
        shooting_complaints_df,
        hist_record_role_concat[hist_record_role_concat["type"] == "SHOTS FIRED"][
            ["nysid_num", "cmplnt_id", "role_desc"]
        ],
        on="cmplnt_id",
    )

    cleaned_hist_record_role_concat = hist_record_role_concat[
        ~(
            (
                hist_record_role_concat["nysid_num"].isin(
                    list(shooting_sf_complaint_match_df["nysid_num"])
                )
            )
            & (
                hist_record_role_concat["id"].isin(
                    list(shooting_sf_complaint_match_df["orig_cmplnt_id"])
                )
            )
        )
    ]

    cleaned_hist_record_role_concat = cleaned_hist_record_role_concat.sort_values(
        ["nysid_num", "cmplnt_id", "type"]
    ).drop_duplicates(["nysid_num", "cmplnt_id"])

    ## criteria 1: nysids who are at least once as a shooter (perp, poi, suspect, pc icard, arrest) since 2021
    cleaned_hist_record_role_concat["occur_dt"] = pd.to_datetime(
        cleaned_hist_record_role_concat["occur_dt"]
    )

    criter_1_nysid_list = list(
        set(
            cleaned_hist_record_role_concat[
                (cleaned_hist_record_role_concat["occur_dt"] >= Start_Date)
                & (
                    cleaned_hist_record_role_concat["role_desc"].str.contains(
                        "Arrest|Perp|Suspect|POI|PC Icard"
                    )
                )
            ].nysid_num
        )
    )

    filtered_hist_record_role_concat = cleaned_hist_record_role_concat[
        cleaned_hist_record_role_concat["nysid_num"].isin(criter_1_nysid_list)
    ]

    ## criteria 2: any involvement since 2020/1/1
    preprocess_criteria_2_df = (
        filtered_hist_record_role_concat[
            filtered_hist_record_role_concat["occur_dt"] >= Start_Date_2020
        ]
        .groupby(["nysid_num"])["id"]
        .count()
        .reset_index()
    )
    all_criterias_df = preprocess_criteria_2_df[preprocess_criteria_2_df["id"] > 1]

    final_nysid_list = list(all_criterias_df.nysid_num)
    final_nysid_list = [
        x for x in final_nysid_list if x not in ["07247239R", "12899291P"]
    ]

    cleaned_final_record_role_concat = cleaned_hist_record_role_concat[
        cleaned_hist_record_role_concat["nysid_num"].isin(final_nysid_list)
    ]  # this is the grip list

    # original df

    final_record_role_concat = hist_record_role_concat[
        hist_record_role_concat["nysid_num"].isin(final_nysid_list)
    ]  # This dataframe contains some records with the same complaint in both shooting and shots fired
    final_record_role_concat["occur_dt"] = pd.to_datetime(
        final_record_role_concat["occur_dt"]
    )

    Total_GRIP_Subjects = len(final_nysid_list)

    user_definded_incidents_start_date = predefined_date

    user_defined_incident_list = cleaned_final_record_role_concat[
        cleaned_final_record_role_concat["occur_dt"]
        >= user_definded_incidents_start_date
    ]

    # Pull all shootings since the predefinded date

    all_shootings_df = nypd.get_data(
        """  SELECT S.SHT_HMCDE_INCDT_ID,
                                             SHTING_CLASS_CD
                                      FROM CID.SHI_SH_INCIDENT S
                                       WHERE {date_filter} AND S.CASE_STAT_CD NOT IN ('6', '8') AND METHD_USE_DESC = 'SHOT' AND SHTING_CLASS_CD in ('1', '2')
                                  """.format(
            date_filter="OCCUR_DT BETWEEN '{}' AND '{:%Y-%m-%d}'".format(
                user_definded_incidents_start_date, End_Date
            )
        )
    )

    all_shootings_df = nypd.clean_data(all_shootings_df)

    Total_Shootings = len(all_shootings_df)

    # Pull all shots fired since the predefinded date

    all_shotsfired_complaints = shotsfired_complaints(
        user_definded_incidents_start_date, End_Date.strftime("%Y-%m-%d")
    )

    if int(user_definded_incidents_start_date.split("-")[0]) <= 2021:

        all_complaint_id_list = list(all_shotsfired_complaints["cmplnt_id"])
        for i in ["202106000570899", "202107900587199"]:
            all_complaint_id_list.append(i)

    else:

        all_complaint_id_list = list(all_shotsfired_complaints["cmplnt_id"])

    # this remove the duplicated for the complaints in both shooting and shots fired
    nysid_complaint_count = (
        final_record_role_concat.groupby(["nysid_num", "cmplnt_id"])["id"]
        .count()
        .reset_index()
        .sort_values("id", ascending=False)
    )
    remove_SF_complaints_df = nysid_complaint_count[nysid_complaint_count["id"] > 1]
    remove_SF_complaints_list = list(
        set(
            remove_SF_complaints_df["cmplnt_id"].apply(
                lambda x: x.split("-")[0]
                + x.split("-")[1]
                + x.split("-")[2].zfill(6)
                + "99"
            )
        )
    )

    cleaned_all_complaint_id_list = [
        x for x in all_complaint_id_list if x not in remove_SF_complaints_list
    ]

    Total_Shots_Fired = len(cleaned_all_complaint_id_list)

    # Shooting for any involvement
    Total_Involvement_Shootings = len(
        set(
            user_defined_incident_list[
                user_defined_incident_list["type"] == "SHOOTING"
            ]["id"]
        )
    )
    Total_Involvement_Shootings_NYSID = len(
        set(
            user_defined_incident_list[
                user_defined_incident_list["type"] == "SHOOTING"
            ]["nysid_num"]
        )
    )
    percent_of_involvement_shootings = (
        str(round(Total_Involvement_Shootings / Total_Shootings * 100, 1)) + "%"
    )
    percent_of_involvement_shootings_NYSID = (
        str(round(Total_Involvement_Shootings_NYSID / Total_GRIP_Subjects * 100, 1))
        + "%"
    )

    # Shooting for trigger puller
    Total_Trigger_Pullers_Shootings = len(
        set(
            user_defined_incident_list[
                (user_defined_incident_list["type"] == "SHOOTING")
                & (
                    user_defined_incident_list["role_desc"].str.contains(
                        "Arrest|Suspect|Perp|POI|PC Icard"
                    )
                )
            ]["id"]
        )
    )
    Total_Trigger_Pullers_Shootings_NYSID = len(
        set(
            user_defined_incident_list[
                (user_defined_incident_list["type"] == "SHOOTING")
                & (
                    user_defined_incident_list["role_desc"].str.contains(
                        "Arrest|Suspect|Perp|POI|PC Icard"
                    )
                )
            ]["nysid_num"]
        )
    )
    percent_of_trigger_pullers_shootings = (
        str(round(Total_Trigger_Pullers_Shootings / Total_Shootings * 100, 1)) + "%"
    )
    percent_of_trigger_pullers_shootings_NYSID = (
        str(round(Total_Trigger_Pullers_Shootings_NYSID / Total_GRIP_Subjects * 100, 1))
        + "%"
    )

    # Combined shootings and shots fired for any involvement
    Total_Involvement_Combined = len(set(user_defined_incident_list["id"]))
    Total_Involvement_Combined_NYSID = len(set(user_defined_incident_list["nysid_num"]))
    percent_of_involvement_combined = (
        str(
            round(
                Total_Involvement_Combined
                / (Total_Shootings + Total_Shots_Fired)
                * 100,
                1,
            )
        )
        + "%"
    )
    percent_of_involvement_combined_NYSID = (
        str(round(Total_Involvement_Combined_NYSID / Total_GRIP_Subjects * 100, 1))
        + "%"
    )

    # Combined shootings and shots fired for trigger puller
    Total_Trigger_Pullers_Combined = len(
        set(
            user_defined_incident_list[
                (
                    user_defined_incident_list["role_desc"].str.contains(
                        "Arrest|Suspect|Perp|POI|PC Icard"
                    )
                )
            ]["id"]
        )
    )
    Total_Trigger_Pullers_Combined_NYSID = len(
        set(
            user_defined_incident_list[
                (
                    user_defined_incident_list["role_desc"].str.contains(
                        "Arrest|Suspect|Perp|POI|PC Icard"
                    )
                )
            ]["nysid_num"]
        )
    )
    percent_of_trigger_pullers_combined = (
        str(
            round(
                Total_Trigger_Pullers_Combined
                / (Total_Shootings + Total_Shots_Fired)
                * 100,
                1,
            )
        )
        + "%"
    )
    percent_of_trigger_pullers_combined_NYSID = (
        str(round(Total_Trigger_Pullers_Combined_NYSID / Total_GRIP_Subjects * 100, 1))
        + "%"
    )

    # Open Felony
    open_case_df = nypd.get_data(
        f""" SELECT DISTINCT NYSID_NUM,
                                             PENAL_CD_CAT_CD
                                       FROM DS.OCA_SUMMARY OCA
                                       LEFT JOIN CID.CCH_CRIMINAL_CHARGE CHG
                                       ON OCA.ARR_ID = CHG.EVNT_ID AND SEQ_NUM = 1
                                       WHERE NYSID_NUM IN {tuple(user_defined_incident_list['nysid_num'])} AND DISP_STATUS = 'Open'"""
    )

    # ----------------------------Shootings----------------------------------------
    shooting_trigger_puller_nysid = list(
        set(
            user_defined_incident_list[
                (user_defined_incident_list["type"] == "SHOOTING")
                & (
                    user_defined_incident_list["role_desc"].str.contains(
                        "Arrest|Suspect|Perp|POI|PC Icard"
                    )
                )
            ]["nysid_num"]
        )
    )

    shooting_involvement_nysid = list(
        set(
            user_defined_incident_list[
                user_defined_incident_list["type"] == "SHOOTING"
            ]["nysid_num"]
        )
    )

    # -----------------------------Combined shootings and shots fired------------------------------------------

    combined_trigger_puller_nysid = list(
        set(
            user_defined_incident_list[
                user_defined_incident_list["role_desc"].str.contains(
                    "Arrest|Suspect|Perp|POI|PC Icard"
                )
            ]["nysid_num"]
        )
    )

    combined_involvement_nysid = list(set(user_defined_incident_list["nysid_num"]))

    # ----------------------------Shootings (open cases)----------------------------------------
    Total_Shooting_Trigger_Puller_Open_Case = len(
        set(
            open_case_df[open_case_df["nysid_num"].isin(shooting_trigger_puller_nysid)][
                "nysid_num"
            ]
        )
    )

    Total_Shooting_Trigger_Puller_Open_Felony_Case = len(
        set(
            open_case_df[
                (open_case_df["nysid_num"].isin(shooting_trigger_puller_nysid))
                & (open_case_df["penal_cd_cat_cd"] == "F")
            ]["nysid_num"]
        )
    )

    percent_of_open_felony_shooting_trigger_puller = (
        str(
            round(
                Total_Shooting_Trigger_Puller_Open_Felony_Case
                / Total_Trigger_Pullers_Shootings_NYSID
                * 100,
                1,
            )
        )
        + "%"
    )

    Total_Shooting_Involvement_Open_Case = len(
        set(
            open_case_df[open_case_df["nysid_num"].isin(shooting_involvement_nysid)][
                "nysid_num"
            ]
        )
    )

    Total_Shooting_Involvement_Open_Felony_Case = len(
        set(
            open_case_df[
                (open_case_df["nysid_num"].isin(shooting_involvement_nysid))
                & (open_case_df["penal_cd_cat_cd"] == "F")
            ]["nysid_num"]
        )
    )

    percent_of_open_felony_shooting_involvement = (
        str(
            round(
                Total_Shooting_Involvement_Open_Felony_Case
                / Total_Involvement_Shootings_NYSID
                * 100,
                1,
            )
        )
        + "%"
    )

    # ----------------------------Combined shootings and shots fired (open cases)----------------------------------------
    Total_Combined_Trigger_Puller_Open_Case = len(
        set(
            open_case_df[open_case_df["nysid_num"].isin(combined_trigger_puller_nysid)][
                "nysid_num"
            ]
        )
    )

    Total_Combined_Trigger_Puller_Open_Felony_Case = len(
        set(
            open_case_df[
                (open_case_df["nysid_num"].isin(combined_trigger_puller_nysid))
                & (open_case_df["penal_cd_cat_cd"] == "F")
            ]["nysid_num"]
        )
    )

    percent_of_open_felony_combined_trigger_puller = (
        str(
            round(
                Total_Combined_Trigger_Puller_Open_Felony_Case
                / Total_Trigger_Pullers_Combined_NYSID
                * 100,
                1,
            )
        )
        + "%"
    )

    Total_Combined_Involvement_Open_Case = len(
        set(
            open_case_df[open_case_df["nysid_num"].isin(combined_involvement_nysid)][
                "nysid_num"
            ]
        )
    )

    Total_Combined_Involvement_Open_Felony_Case = len(
        set(
            open_case_df[
                (open_case_df["nysid_num"].isin(combined_involvement_nysid))
                & (open_case_df["penal_cd_cat_cd"] == "F")
            ]["nysid_num"]
        )
    )

    percent_of_open_felony_combined_involvement = (
        str(
            round(
                Total_Combined_Involvement_Open_Case
                / Total_Involvement_Combined_NYSID
                * 100,
                1,
            )
        )
        + "%"
    )

    print(
        percent_of_involvement_shootings_NYSID
        + " ("
        + str(Total_Involvement_Shootings_NYSID)
        + " out of "
        + str(Total_GRIP_Subjects)
        + ") of the GRIP subjects were involved in "
        + percent_of_involvement_shootings
        + " ("
        + str(Total_Involvement_Shootings)
        + " out of "
        + str(Total_Shootings)
        + ") of the shootings since "
        + user_definded_incidents_start_date
    )
    print(
        str(Total_Shooting_Involvement_Open_Case)
        + " of the "
        + str(Total_Involvement_Shootings_NYSID)
        + " individuals have open cases. "
        + str(Total_Shooting_Involvement_Open_Felony_Case)
        + "("
        + str(percent_of_open_felony_shooting_involvement)
        + ") have open felony cases."
    )

    print(
        percent_of_trigger_pullers_shootings_NYSID
        + " ("
        + str(Total_Trigger_Pullers_Shootings_NYSID)
        + " out of "
        + str(Total_GRIP_Subjects)
        + ") of the GRIP subjects were responsible for "
        + percent_of_trigger_pullers_shootings
        + " ("
        + str(Total_Trigger_Pullers_Shootings)
        + " out of "
        + str(Total_Shootings)
        + ") of the shootings since "
        + user_definded_incidents_start_date
        + "."
    )
    print(
        str(Total_Shooting_Trigger_Puller_Open_Case)
        + " of the "
        + str(Total_Trigger_Pullers_Shootings_NYSID)
        + " individuals have open cases. "
        + str(Total_Shooting_Trigger_Puller_Open_Felony_Case)
        + "("
        + str(percent_of_open_felony_shooting_trigger_puller)
        + ") have open felony cases."
    )

    print(
        percent_of_involvement_combined_NYSID
        + " ("
        + str(Total_Involvement_Combined_NYSID)
        + " out of "
        + str(Total_GRIP_Subjects)
        + ") of the GRIP subjects were involved in "
        + percent_of_involvement_combined
        + " ("
        + str(Total_Involvement_Combined)
        + " out of "
        + str(Total_Shootings + Total_Shots_Fired)
        + ") of the shootings and shots fired since "
        + user_definded_incidents_start_date
    )
    print(
        str(Total_Combined_Involvement_Open_Case)
        + " of the "
        + str(Total_Involvement_Combined_NYSID)
        + " individuals have open cases. "
        + str(Total_Combined_Involvement_Open_Felony_Case)
        + "("
        + str(percent_of_open_felony_combined_involvement)
        + ") have open felony cases."
    )

    print(
        percent_of_trigger_pullers_combined_NYSID
        + " ("
        + str(Total_Trigger_Pullers_Combined_NYSID)
        + " out of "
        + str(Total_GRIP_Subjects)
        + ") of the GRIP subjects were responsible for "
        + percent_of_trigger_pullers_combined
        + " ("
        + str(Total_Trigger_Pullers_Combined)
        + " out of "
        + str(Total_Shootings + Total_Shots_Fired)
        + ") of the shootings and shots fired since "
        + user_definded_incidents_start_date
    )
    print(
        str(Total_Combined_Trigger_Puller_Open_Case)
        + " of the "
        + str(Total_Trigger_Pullers_Combined_NYSID)
        + " individuals have open cases. "
        + str(Total_Combined_Trigger_Puller_Open_Felony_Case)
        + "("
        + str(percent_of_open_felony_combined_trigger_puller)
        + ") have open felony cases."
    )


def make_sql_friedly_list(lst):
    """To pass list into a into an sql query as a prt of f-string that converts it to tuple,
    it has to have at least two items in it"""
    friendly_list = lst.copy()
    while len(friendly_list) < 2:
        friendly_list.append("999")

    return friendly_list


def make_pattern_url(sys_case_num):
    """Given system case number (from ECMS) return a link to the pattern report"""
    return f"https://dashboardsvc/EventDetailReport/(S(5jebudxd3i0zg2v2eoyzsl1s))/DASReportViewer.aspx?ReportType=CustomReport&PatternId={int(sys_case_num)}&UserNm=NYPDFINEST%5cANONYMOUS&IncludeStyle=False&ReportPath=%2fPattern%2fPattern+Report&Random=f2784070a2fa425e99a2981b74b01ca5"


def turn_complaint_number_into_cdw_format(complaint_no):
    "Given a complaint in the format with dashes return complaint in cdw format"
    year, precinct, number = complaint_no.split("-")
    return str(year) + str(precinct).zfill(3) + str(number).lstrip("0").zfill(6) + "99"


def search_database(table_name_fragment="", column_name_fragment="", source="cdw"):
    """Search tables and columns in NYPD's data databases by partial string.
    Author: CRS Megan Tvetenstrand
    """

    import nypd

    sql_cores = {
        "ecms": """

        SELECT      c.name  AS 'ColumnName'
                    ,t.name AS 'TableName'
                    ,s.name AS 'SchemaName'
        FROM        sys.columns c
        JOIN        sys.tables  t   ON c.object_id = t.object_id
        JOIN        sys.schemas  s   ON t.schema_id = s.schema_id
        WHERE       {}
        ORDER BY    SchemaName
                    ,TableName
                    ,ColumnName;     
        """,
        "trails": """

        SELECT      c.name  AS 'ColumnName'
                    ,t.name AS 'TableName'
                    ,s.name AS 'SchemaName'
        FROM        sys.columns c
        JOIN        sys.tables  t   ON c.object_id = t.object_id
        JOIN        sys.schemas  s   ON t.schema_id = s.schema_id
        WHERE       {}
        ORDER BY    SchemaName
                    ,TableName
                    ,ColumnName;     
        """,
        "cdw": """
        select       c.tabschema as schema_name,
                     c.tabname, 
                     c.colname 
        from syscat.columns c
        inner join syscat.tables t on 
              t.tabschema = c.tabschema and t.tabname = c.tabname
        where {}
        and t.type = 'T'
        order by schema_name,
                 tabname,
                 colname;
        """,
    }

    where = []

    if source == "cdw":
        tname, cname = ("c.tabname", "c.colname")

    if source in ["ecms", "trails"]:
        tname, cname = ("t.name", "c.name")

    if table_name_fragment != "":
        where.append(f" {tname} like '%{table_name_fragment}%'")

    if column_name_fragment != "":
        where.append(f" {cname} like '%{column_name_fragment}%'")

    sql = sql_cores[source].format(" or ".join(where))
    print(sql)

    return nypd.get_data(sql, source=source)


def get_911_event_response_times(start_date, end_date, exclude_visibility_patrol=True):
    """911 Events with calculated response times (in seconds) and MODA's incident type categories
    ################################################################################
    *Total response time is calcualted as duration to dispatch (from event create time to dispatch time)
    plus travel duration (from dispatch time to arrival time);
    *Service time is calcuated as response time plus duration from arrival time to event closing time.

    omap_moda_cip_jobs column represents MODA's classification adapted by OMAP:
    (https://www1.nyc.gov/site/911reporting/reports/definitions.page)
        * CRITICAL = Critical Crime in Progress (Shots fired, assist police officer, robbery, burglary,
        larceny from person, assault w/ knife, assault w/ weapon, unusual incident)
        * SERIOUS = Serious Crime in Progress (Auto theft, other larceny, other assault, roving band)
        * NON CRITICAL = Non Crime in Progress (Other crimes in progress)
        * NON CIP = Non Crime in Progress (Incidents that do not constitute a crime in progress. Including, but not
        limited to, crimes that occurred in the past and incidents that are in NYPD's jurisdiction but are not criminal in nature.)
    ################################################################################
    Params:
        start_date (datetime.date or datetime.datetime): minimum date of the 911 records to pull
        end_date (datetime.date or datetime.datetime): maximum date of the 911 records to pull
        exclude_visibility_patrol (bool): whether or not to exclude visibility patrol radio runs that very often have 0s response times
        and will skew average response times towards lower numbers
    Returns:
        events_w_response_times (DataFrame): dataframe for each event with columns for response times
    """

    if exclude_visibility_patrol:
        extra_condition = "AND SUBSTR(AGENCY_EVENT.TYP_CD,1,2) <> '75'"
    else:
        extra_condition = ""

    sql = f"""
    SELECT DISTINCT
        AGENCY_EVENT.CAD_EVNT_ID,
        AGENCY_EVENT.DISP_INC_NUM,
        YEAR(SUBSTR(AGENCY_EVENT.CAD_CREATE_TS,1,10)) AS YEAR,
        MONTHNAME(SUBSTR(AGENCY_EVENT.CAD_CREATE_TS,1,10)) AS MONTH,
        DAYNAME(SUBSTR(AGENCY_EVENT.CAD_CREATE_TS,1,10)) AS DAY_NAME,
        DAY(SUBSTR(AGENCY_EVENT.CAD_CREATE_TS,1,10)) AS DAY,
        (SUBSTR(AGENCY_EVENT.CAD_CREATE_TS,1,10)) AS CREATE_DATE,
        CAD_INCIDENT.INC_TM AS INCIDENT_TIME,
        AGENCY_EVENT.AGENCY_ID,
        AGENCY_EVENT.DISP_GROUP_ID,
        CAD_INCIDENT.NYPD_PCT_CD,
        AGENCY_EVENT.TYP_CD,
        AGENCY_EVENT.TYP_DESC,
        --DISPO_EVENT.DISPO_CD, -- CREATES DUPLICATE VALUES IF USED.
        --DISPO_CODE.DISPO_DESC,
        CASE -- INCLUDES ALL 39
            WHEN (((((((((AGENCY_EVENT.TYP_CD LIKE '%66%') OR (AGENCY_EVENT.TYP_CD LIKE '%10S%')) OR (AGENCY_EVENT.TYP_CD LIKE '%13%')) OR (AGENCY_EVENT.TYP_CD LIKE '%30%')) OR (AGENCY_EVENT.TYP_CD LIKE '%31%')) OR (AGENCY_EVENT.TYP_CD LIKE '%32P%')) OR (AGENCY_EVENT.TYP_CD LIKE '%34K%')) OR (AGENCY_EVENT.TYP_CD LIKE '%34S%')) OR (AGENCY_EVENT.TYP_CD LIKE '%34W%')) THEN 'CRITICAL'
            WHEN ((((AGENCY_EVENT.TYP_CD LIKE '%51%') OR (AGENCY_EVENT.TYP_CD LIKE '%32Q%')) OR (AGENCY_EVENT.TYP_CD LIKE '%32V%')) OR (AGENCY_EVENT.TYP_CD LIKE '%34Q%')) THEN 'SERIOUS'
            WHEN (AGENCY_EVENT.TYP_CD LIKE '%39%') THEN 'NON CRITICAL'
            ELSE 'NON CIP'
            END  AS OMAP_MODA_CIP_JOBS,
        TIMESTAMP(AGENCY_EVENT.ADD_TS)  AS  ADD_TS,
        TIMESTAMP(AGENCY_EVENT.DISP_TS)  AS  DISP_TS,
        TIMESTAMP(AGENCY_EVENT.ARRIVD_TS)  AS  ARRIVD_TS,
        TIMESTAMP(AGENCY_EVENT.CLOSNG_TS)  AS  CLOSNG_TS,
        TIMESTAMPDIFF(2,(TIMESTAMP(AGENCY_EVENT.DISP_TS) - TIMESTAMP(AGENCY_EVENT.ADD_TS)))  AS  TIME_TO_DISP, -- DISPATCH TIME
        TIMESTAMPDIFF(2,(TIMESTAMP(AGENCY_EVENT.ARRIVD_TS) - TIMESTAMP(AGENCY_EVENT.DISP_TS)))  AS  TRAVEL_TIME, --TRAVEL TIME
        TIMESTAMPDIFF(2,(TIMESTAMP(AGENCY_EVENT.ARRIVD_TS) - TIMESTAMP(AGENCY_EVENT.ADD_TS)))  AS  RESPONSE_TIME, --RESPONSE TIME
        TIMESTAMPDIFF(2,(TIMESTAMP(AGENCY_EVENT.CLOSNG_TS) - TIMESTAMP(AGENCY_EVENT.ADD_TS)))  AS  SERVICE_TIME --SERVICE TIME

    FROM 
        ICAD.AGENCY_EVENT AGENCY_EVENT

    LEFT OUTER JOIN
        ICAD.DISPO_EVENT DISPO_EVENT
        ON AGENCY_EVENT.CAD_EVNT_ID = DISPO_EVENT.CAD_EVNT_ID
        AND AGENCY_EVENT.DISP_INC_NUM = DISPO_EVENT.DISP_INC_NUM

    LEFT OUTER JOIN 
        ICAD.CAD_INCIDENT CAD_INCIDENT
        ON CAD_INCIDENT.CAD_EVNT_ID = AGENCY_EVENT.CAD_EVNT_ID

    LEFT OUTER JOIN
        ICAD.DISPO_CODE DISPO_CODE
        ON DISPO_EVENT.DISPO_CD = DISPO_CODE.DISPO_CD

    WHERE 
        SUBSTR(AGENCY_EVENT.CAD_CREATE_TS,1,10) BETWEEN '{start_date:%Y-%m-%d}' AND '{end_date:%Y-%m-%d}'
        AND (CASE 
                WHEN (SUBSTR(DISPO_EVENT.DISPO_CD,1,2) IN ('90','91','92','93','94','95','96','97','99','55')) THEN '1'
                ELSE '2'
                END = 1
            )

        AND AGENCY_EVENT.AGENCY_ID = 'D' --PATROL
        {extra_condition} 
    ORDER BY 
           CAD_EVNT_ID ASC;
    """
    return nypd.get_data(sql, source="sprint", clean=True)


def get_most_recent_residential_address(nysid_list):
    """Given a list of NYSIDs return the address associated with the most recent arrest.
       It will take the next most recent address if the most recent address is not valid (PO Box etc).
    Params:
        A dataframe df contains a column NYSID
    returns:
        A dataframe contains the most recent address in addition to the columns in the input dataframe
    """
    nysid_tuple = tuple(list(nysid_list))

    address = nypd.get_data(
        f"""
                    SELECT    DISTINCT
                              NYSID,
                              PCT,
                              APT_SUITE_NUM,
                              FULL_ADDR_DESC,
                              CITY_NM,
                              STATE_CNTRY_CD
 
                    FROM
                    (
 
                    SELECT    DISTINCT
                              NYSID,
                              ADR.ADDR_PCT_CD PCT,
                              APT_SUITE_NUM,
                              FULL_ADDR_DESC,
                              CITY_NM,
                              STATE_CNTRY_CD,
                              ROW_NUMBER() OVER (PARTITION BY NYSID ORDER BY ADR.EVNT_KEY DESC) AS rn
 
                    FROM
                    (
   
                    SELECT  DISTINCT
                            NYSID_NUM AS NYSID,
                            ARR_KEY ARREST_KEY
                    FROM CID.ARR_ARREST
                    WHERE ARR_VOIDED_FLG = 'N' AND NYSID_NUM IN {nysid_tuple}
 
                    ) Arrest
                    JOIN CID.PSN_PERSON_OCCUR PSN
                    ON   Arrest.ARREST_KEY = PSN.EVNT_KEY AND EVNT_TYP_CD = 'A' AND ROLE_CD = 'A' 
                    JOIN CID.ADR_ADDRESS_OCCUR ADR
                    ON ADR.EVNT_KEY = Arrest.arrest_key AND ADR.EVNT_TYP_CD = 'A' AND ADR.ADDR_TYP_CD = 'H' AND ADR.ROLE_CD = 'A'
                       AND PSN.PRSN_ROLE_SEQ_NUM = ADR.PRSN_ROLE_SEQ_NUM AND ADR.FULL_ADDR_DESC IS NOT NULL AND ADR.FULL_ADDR_DESC NOT LIKE 'PO BOX%'
                       )
                    WHERE rn = 1
                    """,
        clean=True,
    )

    return address


def get_vehicle_info(df):
    """Given a dataframe for last name, first name and DOB to get vehicle and passenger information for the person who have
       B-summons/Accidents for the past 2 years. It also provides the gang name if the person is a gang member.
    Params:
        dataframe df contains the following columns
        Last Name (str): person's last name
        First Name (str): person's first name
        DOB (datetime): person's date of birth
    Returns
    A dataframe with the following attributes in addition to the input dataframe
        NYSID (str)
        Gang Name (str)
        Vehicle Category (str)
        Vin Number (str)
        Vehicle Make (str)
        Model Year (int)
        Model Description (str)
        Color (str)
        Plate Number (str)
        Registration State (str)
        Passenger Name(NYSID)(DOB)(Gang Name) (str)
        Event Type (str)
        Event Date (datetime)
    """

    end_dt = dt.date.today() - dt.timedelta(days=1)
    start_dt = end_dt - relativedelta(years=2)

    def psg_name_concatenate(x):

        return pd.Series(dict(PSG_Name="%s" % "\n".join(x["Name(NYSID)(DOB)(Gang)"])))

    B_summon_date_type = (
        "VIOLATION_DATE BETWEEN '{:%Y-%m-%d}' AND '{:%Y-%m-%d}'".format(
            start_dt, end_dt
        )
    )
    BSummon = nypd.get_data(
        f"""
                               SELECT DISTINCT
                                       TRIM(UPPER(PSN.LAST_NM)) Last_Name,
                                       TRIM(UPPER(PSN.FRST_NM)) First_Name,
                                       PSN.NYSID_NUM,
                                       PSN.BRTH_DT,
                                       VHC.VEH_CATEGORY,
                                       CASE WHEN VHC_MAKE.VEHIC_MAKE_DESC IS NULL THEN VHC.VEH_MAKE_NM
                                            ELSE VHC_MAKE.VEHIC_MAKE_DESC
                                       END AS VHC_MAKE,
                                       VHC.VEH_MODEL_YEAR,
                                       VHC.VEH_MODEL_DESC,
                                       COLOR_DESC,
                                       VHC.REG_PLATE_NUM,
                                       VHC.REG_STATE_CD,
                                       PSN.EVNT_ID,
                                       NULL AS VEH_SEQ_NUM,
                                       'B-Summon' AS EVENT_TYPE,
                                       VIN_NUM,
                                       VIOLATION_DATE DATE,
                                       PSN.EVNT_KEY
                                FROM CID.PSN_PERSON_OCCUR PSN
                                JOIN CID.DMV_INFO_OCCUR DMV
                                ON PSN.EVNT_KEY = DMV.EVNT_KEY AND PSN.EVNT_TYP_CD = 'DMV' AND PSN.ROLE_CD = 'M'
                                LEFT JOIN CID.VHS_VEH_INFO VHC
                                ON VHC.EVNT_KEY = DMV.EVNT_KEY AND VHC.EVNT_TYP_CD = 'DMV' AND VHC.ROLE_CD = 'M'
                                LEFT JOIN CID.VEHIC_MAKE_CD VHC_MAKE
                                ON VHC_MAKE.VEHIC_MAKE_CD = VHC.VEH_MAKE_NM
                                LEFT JOIN CID.COLOR_CD
                                ON COLOR_CD = VHC.COLOR_PRIM_CD
                                WHERE {B_summon_date_type} AND VEH_CATEGORY IN ('CAR/SUV', 'TRUCK/BUS')
                                """,
        clean=True,
    )

    Accident_date_type = "ACC_DT BETWEEN '{:%Y-%m-%d}' AND '{:%Y-%m-%d}'".format(
        start_dt, end_dt
    )
    Accident = nypd.get_data(
        f"""SELECT DISTINCT
                                       TRIM(UPPER(PSN.LAST_NM)) Last_Name,
                                       TRIM(UPPER(PSN.FRST_NM)) First_Name,
                                       PSN.NYSID_NUM,
                                       PSN.BRTH_DT,
                                       VEH.VEH_CATEGORY,
                                       CASE WHEN VHC_MAKE.VEHIC_MAKE_DESC IS NULL THEN VEH.VEH_MAKE_NM
                                            ELSE VHC_MAKE.VEHIC_MAKE_DESC
                                       END AS VHC_MAKE,
                                       VEH.VEH_MODEL_YEAR,
                                       VEH.VEH_MODEL_DESC,
                                       COLOR_DESC,
                                       VEH.REG_PLATE_NUM,
                                       VEH.REG_STATE_CD,
                                       PSN.EVNT_ID,
                                       PSA.VEH_SEQ_NUM,
                                       'Accident' AS EVENT_TYPE,
                                       VIN_NUM,
                                       ACC_DT Date,
                                       PSN.EVNT_KEY
                                FROM CID.PSN_PERSON_OCCUR PSN
                                JOIN CID.PSA_PERSON_ATTRIBUTES PSA
                                ON PSN.EVNT_KEY = PSA.EVNT_KEY AND PSN.PRSN_ROLE_SEQ_NUM = PSA.PRSN_ROLE_SEQ_NUM  AND PSN.EVNT_TYP_CD = 'E' AND PSN.ROLE_CD = PSA.ROLE_CD AND PSN.ROLE_CD = 'M'
                                JOIN CID.VHS_VEH_INFO VEH
                                ON VEH.EVNT_KEY = PSA.EVNT_KEY AND PSA.VEH_SEQ_NUM = VEH.VEH_SEQ_NUM 
                                LEFT JOIN CID.ACC_ACCIDENT A
                                ON VEH.EVNT_KEY = A.ACC_KEY
                                LEFT JOIN CID.VEHIC_MAKE_CD VHC_MAKE
                                ON VHC_MAKE.VEHIC_MAKE_CD = VEH.VEH_MAKE_NM 
                                LEFT JOIN CID.COLOR_CD
                                ON COLOR_CD = VEH.COLOR_PRIM_CD
                                WHERE {Accident_date_type} AND VEH_CATEGORY IN ('CAR/SUV', 'TRUCK/BUS')
                                """,
        clean=True,
    )

    gang_member = nypd.get_data(
        f"""SELECT DISTINCT
                                TRIM(UPPER(CGM.FRST_NM)) First_Name,
                                TRIM(UPPER(CGM.LAST_NM)) Last_Name,
                                CGM.GRP_MEMBER_ID,
                                CGM.GRP_NM,
                                PSN.BRTH_DT,
                                CGM.NYSID
                                FROM CID.CGM_CRIMGRP_MEMBERS CGM
                                LEFT JOIN CID.PSN_PERSON_OCCUR PSN
                                ON CGM.EVNT_KEY = PSN.EVNT_KEY
                                """,
        clean=True,
    )

    passenger = nypd.get_data(
        f"""

        SELECT  PSG_info.FRST_NM || ' ' || PSG_info.LAST_NM NAME,
                CASE WHEN gang_info.NYSID IS NULL THEN 'N/A'
                     ELSE gang_info.NYSID
                END AS NYSID,
                PSG_info.BRTH_DT,
                CASE WHEN gang_info.GRP_NM IS NULL THEN 'N/A'
                     ELSE TRIM(gang_info.GRP_NM)
                END AS GRP_NM,
                TRIM(PSG_info.EVNT_ID) EVNT_ID,
                PSG_info.VEH_SEQ_NUM
                
                
        FROM
        (
         SELECT DISTINCT
               TRIM(UPPER(PSN.LAST_NM)) LAST_NM,
               TRIM(UPPER(PSN.FRST_NM)) FRST_NM,
               PSN.BRTH_DT,
               VEH.VEH_CATEGORY,
               CASE WHEN VHC_MAKE.VEHIC_MAKE_DESC IS NULL THEN VEH.VEH_MAKE_NM
                    ELSE VHC_MAKE.VEHIC_MAKE_DESC
               END AS VHC_MAKE,
               VEH.VEH_MODEL_YEAR,
               VEH.VEH_MODEL_DESC,
               COLOR_DESC,
               VEH.REG_PLATE_NUM,
               VEH.REG_STATE_CD,
               PSN.ROLE_CD,
               PSN.EVNT_ID,
               PSA.VEH_SEQ_NUM
        FROM CID.PSN_PERSON_OCCUR PSN
        JOIN CID.PSA_PERSON_ATTRIBUTES PSA
        ON PSN.EVNT_KEY = PSA.EVNT_KEY AND PSN.PRSN_ROLE_SEQ_NUM = PSA.PRSN_ROLE_SEQ_NUM  AND PSN.EVNT_TYP_CD = 'E' AND PSN.ROLE_CD = PSA.ROLE_CD AND PSN.ROLE_CD ='PSG'
        JOIN CID.VHS_VEH_INFO VEH
        ON VEH.EVNT_KEY = PSA.EVNT_KEY AND PSA.VEH_SEQ_NUM = VEH.VEH_SEQ_NUM 
        LEFT JOIN CID.ACC_ACCIDENT A
        ON VEH.EVNT_KEY = A.ACC_KEY
        LEFT JOIN CID.VEHIC_MAKE_CD VHC_MAKE
        ON VHC_MAKE.VEHIC_MAKE_CD = VEH.VEH_MAKE_NM 
        LEFT JOIN CID.COLOR_CD
        ON COLOR_CD = VEH.COLOR_PRIM_CD
        WHERE {Accident_date_type} AND VEH_CATEGORY IN ('CAR/SUV', 'TRUCK/BUS')
         ) PSG_info
         LEFT JOIN 
        (SELECT DISTINCT
               TRIM(UPPER(CGM.FRST_NM)) FRST_NM,
               TRIM(UPPER(CGM.LAST_NM)) LAST_NM,
               CGM.GRP_MEMBER_ID,
               CGM.GRP_NM,
               PSN.BRTH_DT,
               CGM.NYSID
        FROM CID.CGM_CRIMGRP_MEMBERS CGM
        LEFT JOIN CID.PSN_PERSON_OCCUR PSN
        ON CGM.EVNT_KEY = PSN.EVNT_KEY
        ) gang_info
        ON PSG_info.FRST_NM = gang_info.FRST_NM 
           AND PSG_info.LAST_NM = gang_info.LAST_NM
           AND PSG_info.BRTH_DT = gang_info.BRTH_DT


         """,
        clean=True,
    )

    Event = pd.concat([BSummon, Accident])
    event_passenger = passenger[~passenger.name.isna()]
    # event_passenger['brth_dt'] = event_passenger['brth_dt'].apply(lambda x: x.strftime('%Y-%m-%d'))
    event_passenger.loc[event_passenger["brth_dt"].isna(), "brth_dt"] = "N/A"
    event_passenger["Name(NYSID)(DOB)(Gang)"] = (
        event_passenger["name"]
        + "("
        + event_passenger["nysid"]
        + ")"
        + "("
        + event_passenger["brth_dt"].apply(lambda x: str(x).split(" ")[0])
        + ")"
        + "("
        + event_passenger["grp_nm"]
        + ")"
    )
    passenger_data_info = (
        event_passenger.groupby(["evnt_id", "veh_seq_num"])
        .apply(psg_name_concatenate)
        .reset_index()
    )

    event_vehicle_psg = pd.merge(
        Event, passenger_data_info, how="left", on=["evnt_id", "veh_seq_num"]
    )
    Event_w_ganginfo = pd.merge(
        event_vehicle_psg,
        gang_member,
        how="left",
        on=["last_name", "first_name", "brth_dt"],
    )
    final = Event_w_ganginfo[
        [
            "last_name",
            "first_name",
            "nysid_num",
            "brth_dt",
            "grp_nm",
            "veh_category",
            "vin_num",
            "vhc_make",
            "veh_model_year",
            "veh_model_desc",
            "color_desc",
            "reg_plate_num",
            "reg_state_cd",
            "PSG_Name",
            "event_type",
            "date",
        ]
    ]
    final.drop_duplicates(inplace=True)
    final.columns = [
        "Last Name",
        "First Name",
        "NYSID",
        "DOB",
        "Gang Name",
        "Vehicle Category",
        "Vin Number",
        "Vehicle Make",
        "Model Year",
        "Model Description",
        "Color",
        "Plate Number",
        "Registration State",
        "Passenger Name(NYSID)(DOB)(Gang Name)",
        "Event Type ",
        "Event Date",
    ]

    return pd.merge(df, final, on=["Last Name", "First Name", "DOB"]).sort_values(
        ["Last Name", "First Name", "Event Date"], ascending=[True, True, False]
    )


def add_current_custody(df, nysid_col="nysid_num"):
    """Given a dataframe with NYSID column, add a custody column to the dataframe
    Params:
        df (Pandas dataframe): Dataframe with NYSID column
        col (str): name of the NYSID column
    Returns:
        original dataframe with custody column added
    """
    nysids = df[nysid_col].dropna().unique().tolist()
    while len(nysids) < 2:
        nysids.append("999")

    custody_sql = f"""
        with person_info AS (
            SELECT DISTINCT
                PRSN.NYSID_NUM NYSID
            FROM 
                CID.PSN_PERSON_OCCUR PRSN
            WHERE
                PRSN.NYSID_NUM in {tuple(nysids)}
            ),
            city_custody AS (
                    SELECT
                        PSN.NYSID_NUM NYSID,
                        COUNT(*) AS CITY_CUST_HIST,
                        CASE WHEN (
                            SUM(
                                CASE WHEN (
                                    CITY_CUST.DIS_DATE IS NULL
                                    AND CITY_CUST.INM_DOD_DT IS NULL
                                ) THEN 1 ELSE 0 END
                            )
                        ) > 0 THEN 'Y' ELSE 'N' END AS CITY_CUST_STATUS
                    FROM
                        CID.PSN_PERSON_OCCUR PSN
                    JOIN 
                        CID.CDC_INMATE_NYC CITY_CUST ON 
                        CITY_CUST.BK_CASE_KEY = PSN.EVNT_KEY
                        AND PSN.EVNT_TYP_CD = 'CDC' 
                        AND PSN.ROLE_CD = '7'
                    WHERE
                        CITY_CUST.DIS_DATE IS NULL -- discharge date
                        AND CITY_CUST.INM_DOD_DT IS NULL -- inmate dead on date
                    GROUP BY
                        PSN.NYSID_NUM
                        ),
            state_custody AS (
                    SELECT
                        PSN.NYSID_NUM NYSID,
                        COUNT(*) AS STATE_CUST_HIST,
                        CASE WHEN (
                            SUM(
                                CASE WHEN (PRP.STILL_UNDERCUSTODY_FLG = 'Y') THEN 1 ELSE 0 END
                            )
                        ) > 0 THEN 'Y' ELSE 'N' END AS STATE_CUST_STATUS
                    FROM
                        CID.PSN_PERSON_OCCUR PSN
                    JOIN 
                        CID.PRP_PERP_OCCUR PRP ON 
                        PRP.EVNT_KEY = PSN.EVNT_KEY
                    WHERE
                        PRP.EVNT_TYP_CD = 'DOC'
                        AND PRP.ROLE_CD = '7'
                    GROUP BY
                        PSN.NYSID_NUM
            )
    SELECT 
         person_info.NYSID,
         CASE WHEN city_custody.CITY_CUST_STATUS = 'Y' THEN 'Y' ELSE 'N' END AS CITY_CUST,
         CASE WHEN state_custody.STATE_CUST_STATUS = 'Y' THEN 'Y' ELSE 'N' END AS STATE_CUST
 
    FROM
        person_info
 
    LEFT JOIN 
        city_custody ON 
        city_custody.NYSID = person_info.NYSID
    LEFT JOIN 
        state_custody ON 
        state_custody.NYSID = person_info.NYSID
    """
    custody = nypd.get_data(custody_sql, clean=True)
    custody["custody"] = np.nan
    custody.loc[custody["city_cust"] == "Y", "custody"] = "In City"
    custody.loc[custody["state_cust"] == "Y", "custody"] = "In State"
    custody["custody"] = custody["custody"].fillna("Out")

    return df.merge(
        custody[["nysid", "custody"]].rename(columns={"nysid": nysid_col}),
        on=nysid_col,
        how="left",
    )


def get_on_probation_status(nysid):
    """Given a NYSID return whether the person is currently on probation
    Params:
        nysid (str): person's NYSID
        run_date: the run date
    Returns
        status (bool): True or False
    """

    df = nypd.get_data(
        f"""
    SELECT DISTINCT
            MED_DT,
            PROB.NYSID
        FROM
            CID.PRB_PROBATION PROB
        WHERE
            PROB.CASE_STAT_DESC != 'CLOSED'
            AND PROB.NYSID='{nysid}'
    """,
        clean=True,
    )

    df = df[df["med_dt"] > date.today()]
    df.drop(columns=["med_dt"], inplace=True)

    if not df.empty:
        status = True
    else:
        status = False

    return status


def get_on_parole_status(nysid):
    """Given a NYSID return whether the person is currently on parole
    Params:
        nysid (str): person's NYSID
        run_date: the run date
    Returns
        status (bool): True or False
    """
    df = nypd.get_data(
        f"""
    SELECT DISTINCT
            PAROLE_MAX_EXP_DT,
            PAR.NYSID
        FROM
            STAGE.PAROLE PAR
        WHERE
            PAR.PAROLE_STATUS_FLG = 'A'
            AND PAR.NYSID='{nysid}'
    """,
        clean=True,
    )

    df = df[df["parole_max_exp_dt"] > date.today()]
    df.drop(columns=["parole_max_exp_dt"], inplace=True)

    if not df.empty:
        status = True
    else:
        status = False

    return status


def get_probation_status_during_arrest(arr_id):
    """Given an arrest ID return whether the person was on probation at the time of arrest
    Params:
        arr_id (str): arrest ID
    Return:
        arrested_while_probation (bool): True or False
    """

    arr = nypd.get_data(
        f"""
    SELECT
        ARR.ARR_ID,
        ARR.ARR_DT,
        ARR.NYSID_NUM
    FROM
        CID.ARR_ARREST ARR
    WHERE
        ARR.ARR_ID='{arr_id}'
    """,
        clean=True,
    )
    if arr.empty:
        raise Exception("Valid Arrest ID must be passed")

    nysid = arr["nysid_num"].values[0]
    if pd.isnull(nysid):
        raise Exception(
            f"Arrestee has no NYSID; unable to get probation information for arrest #{arr_id}"
        )

    arr_date = pd.Timestamp(arr["arr_dt"].dt.date.values[0])

    probations = nypd.get_data(
        f"""
    SELECT
        NYSID,
        SENTENCED_DT,
        COALESCE(ANTICIPATED_REL_DT, MED_DT) min_end_dt
    FROM
        CID.PRB_PROBATION
    WHERE
        NYSID='{nysid}'
    """,
        clean=True,
    )

    historic_probations = nypd.get_data(
        f"""
    SELECT
        NYSID,
        SENTENCED_DT,
        COALESCE(ANTICIPATED_REL_DT, MED_DT) min_end_dt
    FROM
        STAGE.PROBATION_HIST
    WHERE
        NYSID='{nysid}'
    """,
        clean=True,
    )

    all_probations = probations.append(historic_probations)

    if not all_probations.empty:
        after_sentence = (
            all_probations["sentenced_dt"].fillna(
                pd.Timestamp(datetime.today() + timedelta(1))
            )
            <= arr_date
        )  # some of the records are missing sentencing date; fill missing with tomorrow's date
        before_expiration = arr_date <= all_probations["min_end_dt"].fillna(
            pd.Timestamp("1700-01-01")
        )  # fill missing with very old date to make sure it won't return false positive for Nulls
        arr_during_prob = all_probations.loc[(after_sentence) & (before_expiration)]
        if not arr_during_prob.empty:
            arrested_while_probation = True
        else:
            arrested_while_probation = False
    else:
        arrested_while_probation = False

    return arrested_while_probation


def get_parole_status_during_arrest(arr_id):
    """Given an arrest ID return whether the person was on parole at the time of arrest
    Params:
        arr_id (str): arrest ID
    Return:
        arrested_while_parole (bool): True or False
    """

    arr = nypd.get_data(
        f"""
    SELECT
        ARR.ARR_ID,
        ARR.ARR_DT,
        ARR.NYSID_NUM
    FROM
        CID.ARR_ARREST ARR
    WHERE
        ARR.ARR_ID='{arr_id}'
    """,
        clean=True,
    )
    if arr.empty:
        raise Exception("Valid Arrest ID must be passed")

    nysid = arr["nysid_num"].values[0]

    if pd.isnull(nysid):
        raise Exception(
            f"Arrestee has no NYSID; unbale to get parole information for arrest #{arr_id}"
        )

    arr_date = pd.Timestamp(arr["arr_dt"].dt.date.values[0])

    paroles = nypd.get_data(
        f"""
    SELECT
        NYSID,
        RELEASE_DT,
        PAROLE_CNL_DT,
        PAROLE_MAX_EXP_DT,
        CASE 
            WHEN PAROLE_CNL_DT > PAROLE_MAX_EXP_DT THEN PAROLE_MAX_EXP_DT
            WHEN PAROLE_CNL_DT IS NULL THEN PAROLE_MAX_EXP_DT
            ELSE PAROLE_CNL_DT
        END AS MIN_END_DT
 
    FROM
        STAGE.PAROLE
    WHERE
         NYSID='{nysid}'
    """,
        clean=True,
    )

    hist_paroles = nypd.get_data(
        f"""
    SELECT
        NYSID,
        RELEASE_DT,
        PAROLE_CNL_DT,
        PAROLE_MAX_EXP_DT,
        CASE 
            WHEN PAROLE_CNL_DT > PAROLE_MAX_EXP_DT THEN PAROLE_MAX_EXP_DT
            WHEN PAROLE_CNL_DT IS NULL THEN PAROLE_MAX_EXP_DT
            ELSE PAROLE_CNL_DT
        END AS MIN_END_DT
 
    FROM
        STAGE.PAROLE_HIST
    WHERE
         NYSID='{nysid}'
    """,
        clean=True,
    )

    all_paroles = paroles.append(hist_paroles)

    if not all_paroles.empty:
        after_sentence = all_paroles["release_dt"] <= arr_date
        before_expiration = arr_date <= all_paroles["min_end_dt"].fillna(
            datetime.today()
        )
        arr_during_parole = all_paroles.loc[(after_sentence) & (before_expiration)]
        if not arr_during_parole.empty:
            arrested_while_parole = True
        else:
            arrested_while_parole = False
    else:
        arrested_while_parole = False

    return arrested_while_parole


def get_parole_info_at_arrest(
    arr_df, arr_id_col="arr_id", arr_dt_col="arr_dt", nysid_col="nysid_num"
):
    """Given a dataframe of arrests, check if arrest was done while perp was on parole
    Params:
        arr_df (dataframe): Dataframe of arrests
        arr_id_col (str): name of the column with arrest ID in the dataframe
        arr_dt (str): name of the column with arrest date in the dataframe
        nysid_col (str): name of the column with NYSID
    Returns:
        original dataframe with parole flag and parole start and end dates added
    """

    nysids = arr_df[nysid_col].dropna().unique().tolist()

    paroles = nypd.get_data(
        f"""
    SELECT
        NYSID,
        RELEASE_DT PAROLE_START_DT,
        PAROLE_CNL_DT,
        PAROLE_MAX_EXP_DT,
        CASE 
            WHEN PAROLE_CNL_DT > PAROLE_MAX_EXP_DT THEN PAROLE_MAX_EXP_DT
            WHEN PAROLE_CNL_DT IS NULL THEN PAROLE_MAX_EXP_DT
            ELSE PAROLE_CNL_DT
        END AS PAROLE_END_DT
 
    FROM
        STAGE.PAROLE
    WHERE
         NYSID in {tuple(nysids)}
    """,
        clean=True,
    )

    hist_paroles = nypd.get_data(
        f"""
    SELECT
        NYSID,
        RELEASE_DT PAROLE_START_DT,
        PAROLE_CNL_DT,
        PAROLE_MAX_EXP_DT,
        CASE 
            WHEN PAROLE_CNL_DT > PAROLE_MAX_EXP_DT THEN PAROLE_MAX_EXP_DT
            WHEN PAROLE_CNL_DT IS NULL THEN PAROLE_MAX_EXP_DT
            ELSE PAROLE_CNL_DT
        END AS PAROLE_END_DT
 
    FROM
        STAGE.PAROLE_HIST
    WHERE
         NYSID in {tuple(nysids)}
    """,
        clean=True,
    )

    all_paroles = paroles.append(hist_paroles, sort=False)
    all_paroles = all_paroles.rename(columns={"nysid": nysid_col})
    cols = [nysid_col, "parole_start_dt", "parole_end_dt"]

    merged = arr_df[[arr_id_col, nysid_col, arr_dt_col]].merge(
        all_paroles[cols], on=nysid_col, how="left"
    )

    arrested_during_parole = (
        merged.loc[
            (merged[arr_dt_col] > merged["parole_start_dt"])
            & (merged[arr_dt_col] < merged["parole_end_dt"])
        ]
        .sort_values([arr_id_col, "parole_end_dt"], ascending=[True, False])
        .drop_duplicates(subset=[arr_id_col])
    )

    arrested_during_parole["arrested_while_parole"] = "Y"

    return arr_df.merge(
        arrested_during_parole, on=["arr_id", "arr_dt", "nysid_num"], how="left"
    )


def get_probation_info_at_arrest(
    arr_df, arr_id_col="arr_id", arr_dt_col="arr_dt", nysid_col="nysid_num"
):
    """Given a dataframe of arrests, check if arrest was done while perp was on probation
    Params:
        arr_df (dataframe): Dataframe of arrests
        arr_id_col (str): name of the column with arrest ID in the dataframe
        arr_dt (str): name of the column with arrest date in the dataframe
        nysid_col (str): name of the column with NYSID
    Returns:
        original dataframe with probation flag and probation start and end dates added
    """

    nysids = arr_df[nysid_col].dropna().unique().tolist()

    probations = nypd.get_data(
        f"""
    SELECT
        NYSID,
        SENTENCED_DT,
        COALESCE(ANTICIPATED_REL_DT, MED_DT) probation_end_dt
    FROM
        CID.PRB_PROBATION
    WHERE
        NYSID in {tuple(nysids)}
    """,
        clean=True,
    )

    historic_probations = nypd.get_data(
        f"""
    SELECT
        NYSID,
        SENTENCED_DT,
        COALESCE(ANTICIPATED_REL_DT, MED_DT) probation_end_dt
    FROM
        STAGE.PROBATION_HIST
    WHERE
        NYSID in {tuple(nysids)}
    """,
        clean=True,
    )

    all_probations = probations.append(historic_probations)

    all_probations = all_probations.rename(columns={"nysid": nysid_col})
    cols = [nysid_col, "sentenced_dt", "probation_end_dt"]

    merged = arr_df[[arr_id_col, nysid_col, arr_dt_col]].merge(
        all_probations[cols], on=nysid_col, how="left"
    )

    arrested_during_probation = (
        merged.loc[
            (merged[arr_dt_col] > merged["sentenced_dt"])
            & (merged[arr_dt_col] < merged["probation_end_dt"])
        ]
        .sort_values([arr_id_col, "probation_end_dt"], ascending=[True, False])
        .drop_duplicates(subset=[arr_id_col])
    )

    arrested_during_probation["arrested_while_probation"] = "Y"

    return arr_df.merge(
        arrested_during_probation, on=["arr_id", "arr_dt", "nysid_num"], how="left"
    )


def make_dummy_image(size=(200, 250)):
    """Create blank image to be used in place of mugshot"""
    empty_image = Image.new("RGB", size, color=(211, 211, 211))
    msg = "Not Available"
    W, H = size
    fontsize = 1  # starting font size
    # portion of image width you want text width to be
    img_fraction = 0.75
    font = ImageFont.truetype("Pillow/Tests/fonts/FreeMono.ttf", fontsize)
    while font.getsize(msg)[0] < img_fraction * empty_image.size[0]:
        # iterate until the text size is just larger than the criteria
        fontsize += 1
        font = ImageFont.truetype("Pillow/Tests/fonts/FreeMono.ttf", fontsize)

    draw = ImageDraw.Draw(empty_image)

    w, h = draw.textsize(msg, font=font)
    draw.text(((W - w) / 2, (H - h) / 2), msg, font=font, fill=(255, 255, 255, 128))
    return empty_image


def get_mugshot(
    key_value,
    database_name="asd",
    key_name="nysid",
    size="large",
    new_size=(200, 250),
    save=True,
    resize=True,
    api_key=None,
):
    """Given a NYSID, fetch latest mugshot from Photomanager (uses latest unsealed arrest).
    Must pass PHOTOMANAGER_API_KEY or have it saved as an environment variable
    """
    requestor_id = "DS"
    if re.match(r"[B|K|Q|S|M]\d{8}", key_value):
        key_name = "arrestnum"
    url = f"https://mugimage.nypd.finest/NYPDPhotoSvc/api/dataRequest/{requestor_id}/{database_name}/{key_name}/{key_value}"

    if not api_key:
        try:
            api_key = os.environ[
                "PHOTOMANAGER_API_KEY"
            ]  # if not passed as parameter, read it from user's environment variables
        except KeyError:
            raise KeyError("Enter the API KEY for the 'DS' user.")

    token = base64.b64encode(f"{requestor_id}:{api_key}".encode()).decode()

    r = requests.get(url, headers={"Authorization": f"Basic {token}"}, verify=False)

    if size == "large" and not resize:
        new_size = (480, 600)

    elif size == "small" and not resize:
        new_size = (144, 180)

    if r.status_code == 200:
        root = ET.fromstring(r.text)

        if "images" in str(root[-1]):

            if size == "large":
                image_key = root[-1][0][0].text
            elif size == "small":
                image_key = root[-1][0][1].text
            else:
                raise ValueError("Size kwarg must be 'large' or 'small'.")

            # Fetch the actual image
            url = f"https://mugimage.nypd.finest/NYPDPhotoSvc/api/imageRequest/{requestor_id}/{image_key}"

            r = requests.get(url, verify=False)
            if r.status_code == 200 and save:
                photo = r.content
                image = BytesIO(photo)
                image_object = Image.open(image)
                if resize:
                    image_object.thumbnail(new_size)
            else:
                image_object = make_dummy_image(size=new_size)

            return image_object
        else:
            return make_dummy_image(size=new_size)
    else:
        return make_dummy_image(size=new_size)


def make_latext_url(html_url):
    """Given HTML url create Latex url"""
    from bs4 import BeautifulSoup as Soup

    html = Soup(html_url, "html.parser")
    url = [a["href"] for a in html.find_all("a")][0]
    anchor = [a.string for a in html.find_all("a")][0]
    return f"\href{{{url}}}{{{anchor}}}"


def make_html_image_tag(image_object):
    """Given PIL image object, encode and return HTML image tag referencing a view that returns the image."""
    buffer = BytesIO()
    image_object.save(buffer, format="PNG")
    buffer.seek(0)
    data_uri = base64.b64encode(buffer.read()).decode("ascii")
    html_img_tag = f'<img src="data:image/png;base64,{data_uri}">'
    return html_img_tag


def make_excell_hyperlink(value):
    """Given HTML url create Excell hyperlink"""
    from bs4 import BeautifulSoup

    soup = BeautifulSoup(value, "html.parser")
    url = soup.find("a").get("href")
    nysid = soup.find("a").text
    return f'=HYPERLINK("{url}", "{nysid}")'


def add_current_age(df, dob_col="brth_dt"):
    """Given DOB return current age
    Params:
        df (DataFrame): dataframe with dob column
        dob_col (str): name of the column that containts dob
    Returns:
        df (DataFrame): dataframe with current_age column added
    """
    days_in_year = 365.2425
    df["current_age"] = np.floor(
        (pd.to_datetime(date.today()) - df[dob_col]).dt.days / days_in_year
    )
    return df


def add_age_on_event(df, event_col, dob_col="brth_dt"):
    """Given the event_date return age of person at the time of an event
        Example: age of person on the time of crime commitment or age of person at the time of an arrest.

    Params:
        df (DataFrame): dataframe with dob column
        dob_col (str): name of the column that containts dob
    Returns:
        df (DataFrame): dataframe with f'{event_col}_age' column added
    """
    days_in_year = 365.2425
    df[f"{event_col}_age"] = np.floor(
        (df[event_col] - df[dob_col]).dt.days / days_in_year
    )
    return df


def create_arrest_link(arrest_id):
    """Gien an arrest ID, return  HTML link to the arrest report in OMNI"""
    url = f"https://omniform.nypd.org/omniform/globalreports/webFocusReport.do?IBIF_ex=VIEWARST&ARRID={arrest_id}"
    return rf'<a href="{url}">{arrest_id}</a>'


def create_uf61_link(complaint_id):
    """Gien an complaint ID, return  HTML link to the complaint report in OMNI"""
    year, pct, cmplnt_num = complaint_id[0:4], complaint_id[4:7], complaint_id[7:13]
    base = "https://omniform.nypd.org/omniform/globalreports/webFocusReport.do?IBIF_webapp=/"
    rest = f"ibi_apps&IBIC_server=EDASERVE&IBIWF_msgviewer=OFF&IBIF_ex=PRNTCOMP&CLICKED_ON=&UF61_YEAR={year}.&UF61_PCT={pct}.&UF61_NUM={cmplnt_num}.&UF61_SEGVER=0."
    return rf'<a href="{base}{rest}">{complaint_id}</a>'


def create_rtrd_link(nysid, tax_id, source="OMNI"):
    """
    The base hyper link is deprecated. Use create_permanent_rtrd_link instead

    Given a NYSID, return a temporary HTML link to the RTRD report
    Params:
        nysid (str): person's NYSID
        tax_id (str): Your Tax ID#

    Returns:
        html_tag (str): a temporary HTML link to the RTRD report -- link will exprire after one day
    """
    hash_str = f"{source}:{tax_id}:{nysid}:{dt.date.today():%m%d%Y}"
    hid = hashlib.sha256((hash_str).encode("utf-8")).hexdigest()
    url = rf"https://s1ppweb8.nypd.finest/RTRD4/RecidivistSummary.aspx?ID={source.lower()}&MOS={tax_id}&NYSID={nysid}&HID={hid}"
    html_tag = r"""<a href="{}">{}</a>""".format(url, nysid)
    return html_tag


def replace_nysids_with_rtrd_links(line):
    """Use regex to find NYSID occurences in the string and replace them with temporary HTML link to RTRD report for that NYSID"""

    def nysid_repl(matchobj):
        return create_permanent_rtrd_link(matchobj.group(0))

    return re.sub(r"\b\d{8}[a-zA-Z]\b", nysid_repl, line)


def create_permanent_rtrd_link(nysid):
    """Given a NYSID, return a permanent  HTML link to the NYSID report"""

    # base_url = "https://s1ppweb8.nypd.finest/RTRD4/RecidivistSummary.aspx?ID=" # the RTRD website has been moved to new host
    base_url = "https://webapps.nypd.org/RTRD/RecidivistSummary.aspx?ID="
    # base_url = "https://omniform.nypd.org/omniform/globalreports/webFocusReport.do?IBIF_ex=REPNYSID&NYSID=" # this is NYSID report

    def encode_nysid(nysid):
        nysid_encoder = {
            "0": "9",
            "1": "8",
            "2": ";",
            "3": ":",
            "4": "=",
            "5": "%3c",
            "6": "6",
            "7": "%3e",
            "8": "1",
            "9": "0",
            "H": "a",
            "J": "c",
            "K": "b",
            "L": "e",
            "M": "d",
            "N": "g",
            "P": "y",
            "Q": "x",
            "R": "%7b",
            "Y": "p",
            "Z": "s",
            "U": "",
            "I": "",
            "S": "",
        }
        encoded_nysid = "".join([nysid_encoder[c] for c in nysid.upper()])
        return encoded_nysid

    encoded_nysid = encode_nysid(nysid)
    url = f"{base_url}{encoded_nysid}"
    # url=f'{base_url}{nysid}' # if want to use NYSUD report in OMNI instead
    html_tag = rf"""<a href="{url}">{nysid}</a>"""
    return html_tag


def replace_nysids_with_permanent_rtrd_links(line):
    """Use regex to find NYSID occurences in the string and replace them with permanent HTML link to RTRD report for that NYSID"""

    def nysid_repl(matchobj):
        return create_permanent_rtrd_link(matchobj.group(0))

    return re.sub(r"\b\d{8}[a-zA-Z]\b", nysid_repl, line)


def send_email(
    sender=None,
    receiver=None,
    cc=None,
    bcc=None,
    subject=None,
    message=None,
    attachments=None,
):
    """Send email with HTML message and attachments to one or many recipients"""

    if attachments is None:
        attachments = []

    if bcc is None:
        bcc = []
    if cc is None:
        cc = []

    def wrap_message_with_tag(message):
        if message and not message.startswith("<"):
            message = f"<p>{message}</p>"
        else:
            message = message
        return message

    if sender is None or subject is None or message is None:
        raise ValueError("The sender, subject and message must not be None.")

    if isinstance(receiver, str):
        receiver = [recipient.strip() for recipient in receiver.split(",")]

    if isinstance(attachments, str):
        attachments = [file.strip() for file in attachments.split(",")]

    msg = EmailMessage()

    if not "@nypd.org" in sender:
        msg["From"] = f"{sender}<domino@nypd.org>"
    else:
        msg["From"] = f"{sender}"

    msg["To"] = ", ".join(receiver)
    if bcc:
        msg["Bcc"] = ", ".join(bcc)
    if cc:
        msg["Cc"] = ", ".join(cc)

    msg["Subject"] = subject
    msg.set_content(wrap_message_with_tag(message), subtype="html")

    # Attachments
    total_size = 0
    for file in attachments:
        total_size += os.path.getsize(file)
        if total_size > (1024 * 1024 * 25):
            raise ValueError("Attachments cannot be greater than 25MB in size.")
        with open(file, "rb") as fp:
            ctype, encoding = mimetypes.guess_type(file)
            if ctype is None or encoding is not None:
                ctype = "application/octet-stream"
            maintype, subtype = ctype.split("/", 1)
            msg.add_attachment(
                fp.read(),
                maintype=maintype,
                subtype=subtype,
                filename=file.split("/")[-1],
            )

    with smtplib.SMTP(host="mailarray.nypd.finest", port=25) as s:
        return s.send_message(msg)


def add_value_labels(
    ax,
    spacing=7,
    text_size=8,
    color="black",
    bar_direction="vertical",
    same_horizontal_label_position=False,
):
    """Add labels to the end of each bar in a bar chart.

    Arguments:
        ax (matplotlib.axes.Axes): The matplotlib object containing the axes
            of the plot to annotate.
        spacing (int): The distance between the labels and the bars.
    """

    # For each bar: Place a label
    rect_order = 0
    max_value = max([patch.get_width() for patch in ax.patches])
    for rect in ax.patches:
        if bar_direction == "vertical":
            # Get X and Y placement of label from rect.
            y_value = rect.get_height()
            x_value = rect.get_x() + rect.get_width() / 2

        elif bar_direction == "horizontal":
            rect_order += 1
            # Get X and Y placement of label from rect.
            y_value = rect.get_y()
            if same_horizontal_label_position:
                x_value = max_value / 2
            else:
                x_value = rect.get_width()
        else:
            raise f"bar_direction must be either 'horisontal' or 'vertical'; instead passed {bar_direction}"

        # Use Y or X value as label and format number with one decimal place
        if bar_direction == "vertical":
            numerical_label = y_value
            label = "{:,.0f}".format(rect.get_height())
        else:
            numerical_label = x_value
            label = "{:,.0f}".format(rect.get_width())

        # Number of points between bar and label. Change to your liking.
        space = spacing
        # Vertical alignment for positive values
        va = "bottom"

        # If value of bar is negative: Place label below bar
        if numerical_label < 0:
            # Invert space to place label below
            space *= -1
            # Vertically align label at top
            va = "top"

        # Create annotation
        ax.annotate(
            label,  # Use `label` as label
            (x_value, y_value),  # Place label at end of the bar
            xytext=(0, space),  # Vertically shift label by `space`
            textcoords="offset points",  # Interpret `xytext` as offset in points
            ha="center",  # Horizontally center label
            va=va,
            size=text_size,
            color=color,
        )  # Vertically align label differently for
        # positive and negative values.


def barh_plot_each_column(df, colors, figsize=(12, 6)):
    """Makes barh chart for each column with each
    column colored according to passed colors;
    Imitates pandas df.style.bar() table styler

    Params:
        df (DataFrame): summary dataframe to plot each column
        colors (dict): column names are keys and colors to use for that column as values
    """
    fig, ax = plt.subplots(nrows=1, ncols=len(df.columns), figsize=figsize)

    for axis, col in zip(ax, df.columns.tolist()):
        df[col].plot(
            ax=axis,
            kind="barh",
            width=1.0,
            facecolor=colors[col],
            edgecolor=colors[col],
            title=col,
            fontsize=12,
            #             alpha=0.5,
        )
        axis.grid(False)
        axis.spines["top"].set_visible(False)
        axis.spines["right"].set_visible(False)
        axis.spines["bottom"].set_visible(False)
        axis.spines["left"].set_visible(False)
        x_axis_label = axis.axes.xaxis.get_label().set_visible(False)
        add_value_labels(
            axis,
            text_size=11,
            bar_direction="horizontal",
            same_horizontal_label_position=True,
        )
        if col == df.columns.tolist()[0]:
            axis.set_xticks([])
            axis.set_yticklabels(df.index.tolist(), fontsize="12")
        else:
            axis.set_xticks([])
            axis.set_yticks([])

    return fig, ax


# https://stackoverflow.com/questions/28931224/adding-value-labels-on-a-matplotlib-bar-chart
def add_value_stacked_labels(ax, text_size=11, color="black"):
    """Add labels to the end of each bar in a bar chart.

    Arguments:
        ax (matplotlib.axes.Axes): The matplotlib object containing the axes
            of the plot to annotate.
        spacing (int): The distance between the labels and the bars.
    """

    # For each bar: Place a label
    for rect in ax.patches:
        # Get X and Y placement of label from rect.
        x_value = rect.get_x() + rect.get_width() / 2
        y_value = rect.get_y() + rect.get_height() / 2

        # Use Y value as label and format number with one decimal place
        label = "{:,.0f}".format(rect.get_height())

        # Create annotation
        ax.annotate(
            label,  # Use `label` as label
            (x_value, y_value),  # Place label at end of the bar
            textcoords="data",  # Interpret `xytext` as offset in points
            ha="center",  # Horizontally center label
            va="bottom",
            size=text_size,
            color=color,
        )  # Vertically align label differently for
        # positive and negative values.


# create table in Compstat style for report
def make_compstat_style_table(df):
    """'Creates a table displaying current vs. prior period stats with percent change in the same cell
    Params:
        df (DataFrame): pandas DataFrame with aggregated data and following columns:
        [7 Day Period, Prior 7 Day Period, 28 Day Period,  Prior 28 Day Period, Year to Date, Prior Year to Date]
    Returns:
        table (DataFrame): pandas DataFrame in Compstat style ready for HTML/Latex export
    """
    table = pd.DataFrame()

    table["7 Day Period"] = (
        df["7 Day Period"].astype(str)
        + " vs. "
        + df["Prior 7 Day Period"].astype(str)
        + "\n"
        + " ("
        + (df["7 Day Period"] - df["Prior 7 Day Period"]).astype(str)
        + ", "
        + round(
            (
                (df["7 Day Period"] - df["Prior 7 Day Period"])
                / df["Prior 7 Day Period"]
                * 100
            ),
            1,
        )
        .replace([np.inf, -np.inf], np.nan)
        .fillna("***.*")
        .astype(str)
        + "%"
        + ")"
    )

    table["28 Day Period"] = (
        df["28 Day Period"].astype(str)
        + " vs. "
        + df["Prior 28 Day Period"].astype(str)
        + "\n"
        + " ("
        + (df["28 Day Period"] - df["Prior 28 Day Period"]).astype(str)
        + ", "
        + round(
            (
                (df["28 Day Period"] - df["Prior 28 Day Period"])
                / df["Prior 28 Day Period"]
                * 100
            ),
            1,
        )
        .replace([np.inf, -np.inf], np.nan)
        .fillna("***.*")
        .astype(str)
        + "%"
        + ")"
    )

    table["Year to Date"] = (
        df["Year to Date"].astype(str)
        + " vs. "
        + df["Prior Year to Date"].astype(str)
        + "\n"
        + " ("
        + (df["Year to Date"] - df["Prior Year to Date"]).astype(str)
        + ", "
        + round(
            (
                (df["Year to Date"] - df["Prior Year to Date"])
                / df["Prior Year to Date"]
                * 100
            ),
            1,
        )
        .replace([np.inf, -np.inf], np.nan)
        .fillna("***.*")
        .astype(str)
        + "%"
        + ")"
    )

    return table


def create_point_shapes(df, x="x_coord", y="y_coord", epsg=2263):
    """Create a point GeoDataframe from passed Dataframe with x,y coordinates

    Params:
        df (DataFrame): pandas DataFrame
        x, y (str): Default values x="x_coord", y="y_coord",
        column names with values for x and y coordinates
        epsg (int): Default value epsg=2263 (NY State Plane ft); EPSG value for the x,y coordinate system
    Returns:
        gdf: (GeoDataFrame) Point GeoDataFrame in the passed Coordinate System
    """
    df_copy = df.copy()
    if df_copy[x].isna().sum() > 0 or df_copy[y].isna().sum() > 0:
        raise Exception(
            f"DataFrame contains Null coordinates; consider removing rows with Null {x, y} values"
        )

    points = [
        Point(xy) for xy in zip(df_copy[x].astype(float), df_copy[y].astype(float))
    ]
    gdf = gpd.GeoDataFrame(
        df_copy,
        geometry=points,
        crs=from_epsg(epsg),
        # crs=CRS(f"epsg:{epsg}") only works with geopandas >0.8
    )
    return gdf


def get_col_widths(dataframe, multi_level_columns=False, index=True):
    """Given a dataframe, return the width (in number of characters) for each column in the dataframe.
    Cab be used to adjust column widths in the excel reports
    """
    # First we find the maximum length of the index column
    if index:
        idx_max = max(
            [len(str(s)) for s in dataframe.index.values]
            + [len(str(dataframe.index.name))]
        )

        if multi_level_columns:
            # will get maximum lengths of either name in multi-level columns or max value length
            return [idx_max] + [
                max([len(str(s)) for s in dataframe[col].values] + [max(map(len, col))])
                for col in dataframe.columns
            ]
        else:
            #  max of the lengths of column name and its values for each column, left to right
            return [idx_max] + [
                max([len(str(s)) for s in dataframe[col].values] + [len(str(col))])
                for col in dataframe.columns
            ]
    else:
        if multi_level_columns:
            # will get maximum lengths of either name in multi-level columns or max value length
            return [
                max([len(str(s)) for s in dataframe[col].values] + [max(map(len, col))])
                for col in dataframe.columns
            ]
        else:
            #  max of the lengths of column name and its values for each column, left to right
            return [
                max([len(str(s)) for s in dataframe[col].values] + [len(str(col))])
                for col in dataframe.columns
            ]


def word_wrap(string, width=80, ind1=0, ind2=0, prefix=""):
    """word wrapping function.
    string: the string to wrap
    width: the column number to wrap at
    prefix: prefix each line with this string (goes before any indentation)
    ind1: number of characters to indent the first line
    ind2: number of characters to indent the rest of the lines
    """
    string = str(string)
    if string != np.nan and string and any([s.isspace() for s in string]):
        string = prefix + ind1 * " " + string
        newstring = ""
        while len(string) > width:
            # find position of nearest whitespace char to the left of "width"
            marker = width - 1
            while not string[marker].isspace():
                marker = marker - 1

            # remove line from original string and add it to the new string
            newline = string[0:marker] + "\n"
            newstring = newstring + newline
            string = prefix + ind2 * " " + string[marker + 1 :]
    else:
        newstring = ""

    return newstring + string


def dedup_kites(kites):
    """Same kite may appear in multiple cases.
    Keep latest of ACTIVE cases for each unique kite id.
    """
    kites["close_date_new"] = kites["close_date"].fillna(today.date())
    clean_kites = (
        kites.sort_values(
            ["key_display", "close_date_new", "created_date"],
            ascending=[False, False, False],
        )
        .drop_duplicates(subset="key_display", keep="first")
        .drop("close_date_new", 1)
    )
    return clean_kites


def format_dates_as_strings(df):
    """Every datetime column in the dataframe will be converted to string;
    Usefull for writing dataframe to Excel/CSV/Shapefile file formats.
    """

    df_copy = df.copy()
    from pandas.api.types import is_datetime64_any_dtype as is_datetime

    date_cols = [column for column in df.columns if is_datetime(df[column])]
    df_copy[date_cols] = df_copy[date_cols].astype(str).replace("NaT", np.nan)
    return df_copy


def membership_map(s: pd.Series, groups: dict, fillvalue: Any = -1) -> pd.Series:
    """
    Map lists of values to catergories.

    use instead of df.loc[value.isin(some_category_list), 'group']='some_group'
    """
    # from RealPython.org
    # Reverse & expand the dictionary key-value pairs
    groups = {x: k for k, v in groups.items() for x in v}
    return s.map(groups).fillna(fillvalue)


def get_employee_image(tax_num: str):
    """Given employee's tax number, fetch employee's image"""

    df = nypd.get_data(
        f"""select tax_id, photo from cid.ros_photo where tax_id = '{tax_num}'"""
    )
    if not df.empty:
        image = Image.open(BytesIO(df.photo.values[0]))
        return image
    else:
        return f"No image found for tax number {tax_num}"


# def geocode_address_or_intersection(adress_string, address_type='street_address'):
#     """Given a street address or intersection of two streets, geocode the location.
#     Address must be passed as a single string value in the proper format.

#     Params:
#         adress_string (str): Properly formatted address. See format examples below.
#         address_type (str): Either 'street_address' or 'intersection'. Defines which rest call to make.
#         street_address should be in the format 'street_num street_name, borough'
#         intersection should be iin the format 'street1, street2, borough'

#     Returns:
#         A dictionary with latitude, longtitude, and x,y coordinates.
#         X,Y coordinates are in New York State Plane (ft) coordinate system.

#     Examples of properly formatted addresses:
#         street_address: 29-14 30 AVENUE, QUEENS'
#         intersection: 'ARTHUR KILL ROAD, VETERANS ROAD WEST, STATEN ISLAND'
#     """

#     def geocode(api_call, lat_str, lon_str, x_string, y_string):
#         response=requests.get(api_call, verify=False)
# #         print(response.status_code)

#         if len(response.json()['candidates'])>0:
#             best_candidate_attributes=response.json()['candidates'][0]['attributes']
#             lat=round(float(best_candidate_attributes[lat_str]), 6)
#             lon=round(float(best_candidate_attributes[lon_str]), 6)
#             X=round(float(best_candidate_attributes[x_string]), 0)
#             Y=round(float(best_candidate_attributes[y_string]), 0)

#             # sometimes lat and lons are zeros but state plane coordinates are valid, if that happens than reproject x,y to get lat, lon
#             if (lat == 0 or lon == 0) and (X!=0):
#                 project = pyproj.Transformer.from_proj(
#                 pyproj.Proj('EPSG:2263'), # source coordinate system
#                 pyproj.Proj('EPSG:4326')) # destination coordinate system
#                 point_st=Point(X, Y)
#                 point_st_wgs = transform(project.transform, point_st)
#                 lat, lon =point_st_wgs.coords.xy[0][0], point_st_wgs.coords.xy[1][0]


#             coords={
#             'lat': lat,
#             'lon': lon,
#             "x_coord": X,
#             "y_coord": Y
#             }

#         else:
#             coords={
#             'lat': np.nan,
#             'lon': np.nan,
#             "x_coord": np.nan,
#             "y_coord": np.nan
#             }

#         return coords

#     pieces=list(map(lambda x:  x.strip(), adress_string.split(',')))

#     if address_type=='intersection':
#         lat_str, lon_str, x_string, y_string='latitude', 'longitude', 'xCoordinate', 'yCoordinate'
#         intersection_base = f"""https://arcgis.nypd.org/portal/sharing/servers/c8826a307e6f4b73bc6098e7f5fe2d4f/rest/services/locateNYC/v1/GeocodeServer/findAddressCandidates?"""
#         intersection = f"""crossStreetOne={pieces[0].replace(' ', '+')}&crossStreetTwo={pieces[1].replace(' ', '+')}&borough={pieces[2].replace(' ', '+')}&outFields=*&outSR=4326&f=json
#         """
#         api_call = intersection_base + intersection

#     elif address_type=='street_address':
#         lat_str, lon_str, x_string, y_string='LAT', 'LONG', 'X', 'Y'

#         address_base="https://arcgis.nypd.org/geocode/rest/services/NYCAddress/GeocodeServer/findAddressCandidates?Address="
#         adress_param=", ".join(pieces).replace(',', '').replace(' ', '+')
#         base_end="&outFields=*&outSR=4326&f=json"

#         api_call = address_base + adress_param+base_end

#     return geocode(api_call, lat_str, lon_str, x_string, y_string)


def geocode_address_or_intersection(adress_string, address_type="street_address"):
    """Given a street address or intersection of two streets, geocode the location.
    Address must be passed as a single string value in the proper format.

    Params:
        adress_string (str): Properly formatted address. See format examples below.
        address_type (str): Either 'street_address' or 'intersection'. Defines which rest call to make.
        street_address should be in the format 'street_num street_name, borough'
        intersection should be iin the format 'street1, street2, borough'

    Returns:
        X,Y coordinates in New York State Plane (ft) coordinate system.

    Examples of properly formatted addresses:
        street_address: 29-14 30 AVENUE, QUEENS'
        intersection: 'ARTHUR KILL ROAD, VETERANS ROAD WEST, STATEN ISLAND'
    """

    def geocode(api_call, x_string, y_string):
        response = requests.get(api_call, verify=False)
        #         print(response.status_code)

        if len(response.json()["candidates"]) > 0:
            best_candidate_attributes = response.json()["candidates"][0]["attributes"]
            X = round(float(best_candidate_attributes[x_string]), 0)
            Y = round(float(best_candidate_attributes[y_string]), 0)

        else:
            X, Y = np.nan, np.nan  # this is most likely address outside NYC

        return X, Y

    pieces = list(map(lambda x: x.strip(), adress_string.split(",")))

    if address_type == "intersection":
        x_string, y_string = "xCoordinate", "yCoordinate"
        intersection_base = f"""https://arcgis.nypd.org/portal/sharing/servers/c8826a307e6f4b73bc6098e7f5fe2d4f/rest/services/locateNYC/v1/GeocodeServer/findAddressCandidates?"""
        intersection = f"""crossStreetOne={pieces[0].replace(' ', '+')}&crossStreetTwo={pieces[1].replace(' ', '+')}&borough={pieces[2].replace(' ', '+')}&outFields=*&outSR=4326&f=json
        """
        api_call = intersection_base + intersection

    elif address_type == "street_address":
        x_string, y_string = "X", "Y"

        address_base = "https://arcgis.nypd.org/geocode/rest/services/NYCAddress/GeocodeServer/findAddressCandidates?Address="
        adress_param = ", ".join(pieces).replace(",", "").replace(" ", "+")
        base_end = "&outFields=*&outSR=4326&f=json"

        api_call = address_base + adress_param + base_end

    return geocode(api_call, x_string, y_string)
