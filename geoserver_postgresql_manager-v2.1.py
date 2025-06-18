"""
GeoServer & PostgreSQL 完整集成管理系统 - 改进版
解决GDAL依赖问题，使用纯Python库，添加完整日志功能
版本: V2.1
"""

import sys
import os
import json
import re
import traceback
import tempfile
import shutil
import zipfile
from pathlib import Path
from datetime import datetime
import xml.etree.ElementTree as ET
from urllib.parse import quote
import logging
from logging.handlers import RotatingFileHandler
import threading
import time

# 核心依赖
import requests
import psycopg2
from psycopg2.extras import RealDictCursor

# 空间数据处理库
try:
    import geopandas as gpd
    import fiona
    import rasterio
    from rasterio.crs import CRS
    from shapely.geometry import Point, LineString, Polygon
    HAS_SPATIAL_LIBS = True
except ImportError:
    HAS_SPATIAL_LIBS = False
    print("警告: 缺少空间数据处理库，请安装: pip install geopandas fiona rasterio")

from PyQt6.QtWidgets import (
    QApplication, QMainWindow, QWidget, QVBoxLayout, QHBoxLayout,
    QTabWidget, QTreeWidget, QTreeWidgetItem, QLineEdit, QTextEdit,
    QPushButton, QLabel, QGroupBox, QComboBox, QProgressBar,
    QMessageBox, QFileDialog, QTableWidget, QTableWidgetItem,
    QHeaderView, QSplitter, QFormLayout, QCheckBox, QSpinBox,
    QDateEdit, QFrame, QScrollArea, QGridLayout, QRadioButton,
    QButtonGroup, QListWidget, QDialog, QDialogButtonBox
)
from PyQt6.QtCore import (
    Qt, QThread, pyqtSignal, QTimer, QSize, QDate, QThreadPool, QRunnable
)
from PyQt6.QtGui import QIcon, QFont, QPixmap, QPalette, QColor

# ================== 日志配置 ==================

class LogManager:
    """日志管理器"""
    
    def __init__(self, log_dir="logs"):
        self.log_dir = Path(log_dir)
        self.log_dir.mkdir(exist_ok=True)
        
        # 设置日志格式
        self.formatter = logging.Formatter(
            '%(asctime)s - %(name)s - %(levelname)s - %(message)s'
        )
        
        # 创建主日志记录器
        self.logger = logging.getLogger('GeoSpatialManager')
        self.logger.setLevel(logging.DEBUG)
        
        # 清除已有的处理器
        self.logger.handlers.clear()
        
        # 添加文件处理器（轮转日志）
        file_handler = RotatingFileHandler(
            self.log_dir / 'application.log',
            maxBytes=10*1024*1024,  # 10MB
            backupCount=5
        )
        file_handler.setLevel(logging.DEBUG)
        file_handler.setFormatter(self.formatter)
        self.logger.addHandler(file_handler)
        
        # 添加错误日志文件
        error_handler = RotatingFileHandler(
            self.log_dir / 'errors.log',
            maxBytes=5*1024*1024,  # 5MB
            backupCount=3
        )
        error_handler.setLevel(logging.ERROR)
        error_handler.setFormatter(self.formatter)
        self.logger.addHandler(error_handler)
        
        # 添加控制台处理器
        console_handler = logging.StreamHandler()
        console_handler.setLevel(logging.INFO)
        console_handler.setFormatter(self.formatter)
        self.logger.addHandler(console_handler)
        
        self.logger.info("日志系统初始化完成")
    
    def get_logger(self, name=None):
        """获取日志记录器"""
        if name:
            return logging.getLogger(f'GeoSpatialManager.{name}')
        return self.logger
    
    def log_operation(self, operation, details, success=True, error=None):
        """记录操作日志"""
        level = logging.INFO if success else logging.ERROR
        message = f"操作: {operation} | 详情: {details}"
        if error:
            message += f" | 错误: {error}"
        
        self.logger.log(level, message)
    
    def log_exception(self, operation, exception):
        """记录异常日志"""
        self.logger.error(f"操作异常: {operation}")
        self.logger.error(f"异常信息: {str(exception)}")
        self.logger.error(f"异常堆栈: {traceback.format_exc()}")

# 全局日志管理器
log_manager = LogManager()
logger = log_manager.get_logger()

# ================== 空间数据处理引擎 ==================

class ImprovedSpatialDataProcessor:
    """改进的空间数据处理器 - 使用纯Python库"""
    
    def __init__(self):
        self.logger = log_manager.get_logger('SpatialProcessor')
        self.temp_dir = None
        
        if not HAS_SPATIAL_LIBS:
            self.logger.error("缺少必要的空间数据处理库")
            raise ImportError("请安装空间数据处理库: pip install geopandas fiona rasterio")
    
    def __enter__(self):
        self.temp_dir = tempfile.mkdtemp(prefix='spatial_data_')
        self.logger.debug(f"创建临时目录: {self.temp_dir}")
        return self
        
    def __exit__(self, exc_type, exc_val, exc_tb):
        if self.temp_dir and os.path.exists(self.temp_dir):
            shutil.rmtree(self.temp_dir)
            self.logger.debug(f"清理临时目录: {self.temp_dir}")
    
    def detect_geometry_type(self, file_path):
        """检测几何类型"""
        try:
            self.logger.debug(f"检测几何类型: {file_path}")
            
            # 使用fiona读取文件信息
            with fiona.open(file_path) as src:
                if src.schema and 'geometry' in src.schema:
                    geom_type = src.schema['geometry']
                    self.logger.info(f"检测到几何类型: {geom_type}")
                    return geom_type.upper()
                    
        except Exception as e:
            self.logger.warning(f"检测几何类型失败: {e}")
            
        return 'GEOMETRY'  # 默认值
    
    def detect_crs(self, file_path):
        """检测坐标参考系统"""
        try:
            self.logger.debug(f"检测坐标系: {file_path}")
            
            file_ext = Path(file_path).suffix.lower()
            
            if file_ext in ['.shp', '.geojson', '.gpkg']:
                # 矢量数据
                with fiona.open(file_path) as src:
                    if src.crs:
                        # 转换为EPSG代码
                        crs_info = src.crs
                        if 'init' in crs_info:
                            epsg_code = crs_info['init']
                            self.logger.info(f"检测到坐标系: {epsg_code}")
                            return epsg_code.upper()
                        elif 'EPSG' in str(crs_info):
                            # 从字符串中提取EPSG代码
                            match = re.search(r'EPSG:(\d+)', str(crs_info))
                            if match:
                                epsg_code = f"EPSG:{match.group(1)}"
                                self.logger.info(f"检测到坐标系: {epsg_code}")
                                return epsg_code
                                
            elif file_ext in ['.tif', '.tiff']:
                # 栅格数据
                with rasterio.open(file_path) as src:
                    if src.crs:
                        crs = CRS.from_wkt(src.crs.to_wkt())
                        if crs.to_epsg():
                            epsg_code = f"EPSG:{crs.to_epsg()}"
                            self.logger.info(f"检测到坐标系: {epsg_code}")
                            return epsg_code
                            
        except Exception as e:
            self.logger.warning(f"坐标系检测失败: {e}")
            
        return "EPSG:4326"  # 默认值
    
    def get_data_extent(self, file_path):
        """获取数据范围"""
        try:
            self.logger.debug(f"获取数据范围: {file_path}")
            
            file_ext = Path(file_path).suffix.lower()
            
            if file_ext in ['.shp', '.geojson', '.gpkg']:
                # 矢量数据
                gdf = gpd.read_file(file_path)
                bounds = gdf.total_bounds
                extent = {
                    'minx': float(bounds[0]),
                    'miny': float(bounds[1]),
                    'maxx': float(bounds[2]),
                    'maxy': float(bounds[3])
                }
                self.logger.info(f"数据范围: {extent}")
                return extent
                
            elif file_ext in ['.tif', '.tiff']:
                # 栅格数据
                with rasterio.open(file_path) as src:
                    bounds = src.bounds
                    extent = {
                        'minx': float(bounds.left),
                        'miny': float(bounds.bottom),
                        'maxx': float(bounds.right),
                        'maxy': float(bounds.top)
                    }
                    self.logger.info(f"数据范围: {extent}")
                    return extent
                    
        except Exception as e:
            self.logger.warning(f"获取数据范围失败: {e}")
            
        return None
    
    def validate_srid(self, srid):
        """验证SRID有效性"""
        try:
            # 使用rasterio的CRS验证
            from rasterio.crs import CRS
            crs = CRS.from_epsg(srid)
            return crs.is_valid
        except:
            return False
    
    def get_file_info(self, file_path):
        """获取文件完整信息"""
        try:
            file_ext = Path(file_path).suffix.lower()
            file_size = os.path.getsize(file_path)
            
            info = {
                'path': file_path,
                'name': Path(file_path).stem,
                'extension': file_ext,
                'size': file_size,
                'size_formatted': self.format_file_size(file_size),
                'type': self.get_data_type(file_ext),
                'geometry_type': None,
                'crs': None,
                'extent': None,
                'feature_count': None
            }
            
            if file_ext in ['.shp', '.geojson', '.gpkg']:
                # 矢量数据详细信息
                info['geometry_type'] = self.detect_geometry_type(file_path)
                info['crs'] = self.detect_crs(file_path)
                info['extent'] = self.get_data_extent(file_path)
                
                # 获取要素数量
                try:
                    gdf = gpd.read_file(file_path)
                    info['feature_count'] = len(gdf)
                except:
                    pass
                    
            elif file_ext in ['.tif', '.tiff']:
                # 栅格数据详细信息
                info['crs'] = self.detect_crs(file_path)
                info['extent'] = self.get_data_extent(file_path)
                
                try:
                    with rasterio.open(file_path) as src:
                        info['bands'] = src.count
                        info['width'] = src.width
                        info['height'] = src.height
                        info['dtype'] = str(src.dtypes[0])
                except:
                    pass
            
            return info
            
        except Exception as e:
            self.logger.error(f"获取文件信息失败 {file_path}: {e}")
            return None
    
    def get_data_type(self, file_ext):
        """根据文件扩展名判断数据类型"""
        vector_extensions = {'.shp', '.geojson', '.kml', '.gpkg', '.gml'}
        raster_extensions = {'.tif', '.tiff', '.img', '.jp2', '.png', '.jpg'}
        
        if file_ext in vector_extensions:
            return "矢量数据"
        elif file_ext in raster_extensions:
            return "栅格数据"
        else:
            return "未知类型"
    
    def format_file_size(self, size_bytes):
        """格式化文件大小"""
        if size_bytes == 0:
            return "0 B"
        size_names = ["B", "KB", "MB", "GB", "TB"]
        import math
        i = int(math.floor(math.log(size_bytes, 1024)))
        p = math.pow(1024, i)
        s = round(size_bytes / p, 2)
        return f"{s} {size_names[i]}"

class ImprovedPostgreSQLManager:
    """改进的PostgreSQL数据管理器"""
    
    def __init__(self, connection_params):
        self.params = connection_params
        self.connection = None
        self.logger = log_manager.get_logger('PostgreSQLManager')
        
    def connect(self):
        """建立连接"""
        try:
            self.logger.info(f"尝试连接PostgreSQL: {self.params['host']}:{self.params['port']}")
            self.connection = psycopg2.connect(**self.params)
            self.connection.autocommit = False
            
            # 检查PostGIS扩展
            cursor = self.connection.cursor()
            cursor.execute("SELECT EXISTS(SELECT 1 FROM pg_extension WHERE extname='postgis')")
            has_postgis = cursor.fetchone()[0]
            cursor.close()
            
            if not has_postgis:
                self.logger.warning("PostGIS扩展未安装")
                return False, "PostGIS扩展未安装"
            
            self.logger.info("PostgreSQL连接成功")
            return True, "连接成功"
            
        except Exception as e:
            self.logger.error(f"数据库连接失败: {e}")
            return False, str(e)
    
    def check_table_exists(self, table_name, schema='public'):
        """检查表是否存在"""
        try:
            cursor = self.connection.cursor()
            cursor.execute("""
                SELECT EXISTS (
                    SELECT 1 FROM information_schema.tables 
                    WHERE table_schema = %s AND table_name = %s
                )
            """, (schema, table_name))
            
            exists = cursor.fetchone()[0]
            cursor.close()
            return exists
            
        except Exception as e:
            self.logger.error(f"检查表存在性失败: {e}")
            return False
    
    def drop_table_if_exists(self, table_name, schema='public'):
        """删除表（如果存在）"""
        try:
            cursor = self.connection.cursor()
            cursor.execute(f'DROP TABLE IF EXISTS "{schema}"."{table_name}" CASCADE')
            self.connection.commit()
            cursor.close()
            self.logger.info(f"删除表: {schema}.{table_name}")
            return True
        except Exception as e:
            self.logger.error(f"删除表失败: {e}")
            self.connection.rollback()
            return False
    
    def import_geodataframe_to_postgis(self, gdf, table_name, schema='public', 
                                     if_exists='replace', index=False):
        """将GeoDataFrame导入到PostGIS"""
        try:
            # 构建连接字符串
            engine_string = (
                f"postgresql://{self.params['user']}:{self.params['password']}"
                f"@{self.params['host']}:{self.params['port']}/{self.params['database']}"
            )
            
            # 使用geopandas的to_postgis方法
            gdf.to_postgis(
                table_name,
                engine_string,
                schema=schema,
                if_exists=if_exists,
                index=index
            )
            
            # 创建空间索引
            self.create_spatial_index(table_name, schema)
            
            self.logger.info(f"成功导入GeoDataFrame到表: {schema}.{table_name}")
            return True, "导入成功"
            
        except Exception as e:
            self.logger.error(f"导入GeoDataFrame失败: {e}")
            return False, str(e)
    
    def import_vector_file(self, file_path, table_name, schema='public', 
                          target_crs='EPSG:4326', overwrite=True):
        """导入矢量文件到PostGIS"""
        try:
            self.logger.info(f"开始导入矢量文件: {file_path} -> {schema}.{table_name}")
            
            # 读取矢量数据
            gdf = gpd.read_file(file_path)
            
            # 检查是否有几何列
            if gdf.geometry.empty:
                return False, "文件中没有几何数据"
            
            # 转换坐标系
            if gdf.crs is None:
                self.logger.warning(f"文件没有坐标系信息，假设为: {target_crs}")
                gdf.set_crs(target_crs, inplace=True)
            elif str(gdf.crs) != target_crs:
                self.logger.info(f"坐标系转换: {gdf.crs} -> {target_crs}")
                gdf = gdf.to_crs(target_crs)
            
            # 确保几何列名为'geom'
            if gdf.geometry.name != 'geom':
                gdf = gdf.rename_geometry('geom')
            
            # 处理字段名（PostgreSQL要求小写）
            column_mapping = {}
            for col in gdf.columns:
                if col != 'geom':
                    clean_col = re.sub(r'[^a-zA-Z0-9_]', '_', col.lower())
                    column_mapping[col] = clean_col
            
            if column_mapping:
                gdf = gdf.rename(columns=column_mapping)
            
            # 检查表是否存在
            if overwrite and self.check_table_exists(table_name, schema):
                self.drop_table_if_exists(table_name, schema)
            
            # 导入到PostGIS
            if_exists = 'replace' if overwrite else 'append'
            success, message = self.import_geodataframe_to_postgis(
                gdf, table_name, schema, if_exists
            )
            
            if success:
                log_manager.log_operation(
                    f"导入矢量文件", 
                    f"{file_path} -> {schema}.{table_name}, {len(gdf)} 个要素",
                    True
                )
            
            return success, message
            
        except Exception as e:
            log_manager.log_exception(f"导入矢量文件", e)
            return False, str(e)
    
    def import_raster_file(self, file_path, table_name, schema='public', 
                          target_crs='EPSG:4326', overwrite=True):
        """导入栅格文件到PostGIS"""
        try:
            self.logger.info(f"开始导入栅格文件: {file_path} -> {schema}.{table_name}")
            
            # 这里可以实现栅格数据导入
            # 由于栅格导入相对复杂，这里先返回一个提示
            self.logger.warning("栅格数据导入功能待实现")
            return False, "栅格数据导入功能暂未实现，请使用矢量数据"
            
        except Exception as e:
            log_manager.log_exception(f"导入栅格文件", e)
            return False, str(e)
    
    def create_spatial_index(self, table_name, schema='public', geom_column='geom'):
        """创建空间索引"""
        try:
            cursor = self.connection.cursor()
            index_name = f"idx_{table_name}_{geom_column}"
            cursor.execute(f'''
                CREATE INDEX IF NOT EXISTS "{index_name}" 
                ON "{schema}"."{table_name}" 
                USING GIST ("{geom_column}")
            ''')
            self.connection.commit()
            cursor.close()
            self.logger.info(f"创建空间索引: {index_name}")
            return True
        except Exception as e:
            self.logger.error(f"创建空间索引失败: {e}")
            self.connection.rollback()
            return False
    
    def rename_table(self, old_name, new_name, schema='public'):
        """重命名表"""
        try:
            cursor = self.connection.cursor()
            cursor.execute(f'ALTER TABLE "{schema}"."{old_name}" RENAME TO "{new_name}"')
            self.connection.commit()
            cursor.close()
            
            log_manager.log_operation(
                "重命名表", 
                f"{schema}.{old_name} -> {schema}.{new_name}",
                True
            )
            return True, "重命名成功"
            
        except Exception as e:
            log_manager.log_exception("重命名表", e)
            self.connection.rollback()
            return False, str(e)
    
    def get_spatial_tables(self):
        """获取空间数据表"""
        if not self.connection:
            return []
            
        try:
            cursor = self.connection.cursor(cursor_factory=RealDictCursor)
            cursor.execute("""
                SELECT 
                    t.table_schema,
                    t.table_name,
                    g.f_geometry_column,
                    g.type as geometry_type,
                    g.srid,
                    pg_size_pretty(pg_total_relation_size(quote_ident(t.table_schema)||'.'||quote_ident(t.table_name))) as table_size,
                    (SELECT COUNT(*) FROM information_schema.columns 
                     WHERE table_schema = t.table_schema AND table_name = t.table_name) as column_count
                FROM information_schema.tables t
                JOIN geometry_columns g ON t.table_name = g.f_table_name 
                    AND t.table_schema = g.f_table_schema
                WHERE t.table_type = 'BASE TABLE'
                    AND t.table_schema NOT IN ('information_schema', 'pg_catalog')
                ORDER BY t.table_schema, t.table_name
            """)
            
            tables = cursor.fetchall()
            cursor.close()
            return tables
            
        except Exception as e:
            self.logger.error(f"获取空间表失败: {e}")
            return []
    
    def get_all_tables(self):
        """获取所有数据表"""
        if not self.connection:
            return []
            
        try:
            cursor = self.connection.cursor(cursor_factory=RealDictCursor)
            cursor.execute("""
                SELECT 
                    t.table_schema,
                    t.table_name,
                    t.table_type,
                    CASE WHEN g.f_table_name IS NOT NULL THEN true ELSE false END as is_spatial,
                    g.type as geometry_type,
                    g.srid,
                    pg_size_pretty(pg_total_relation_size(quote_ident(t.table_schema)||'.'||quote_ident(t.table_name))) as table_size,
                    (SELECT COUNT(*) FROM information_schema.columns 
                     WHERE table_schema = t.table_schema AND table_name = t.table_name) as column_count
                FROM information_schema.tables t
                LEFT JOIN geometry_columns g ON t.table_name = g.f_table_name 
                    AND t.table_schema = g.f_table_schema
                WHERE t.table_type = 'BASE TABLE'
                    AND t.table_schema NOT IN ('information_schema', 'pg_catalog')
                ORDER BY t.table_schema, t.table_name
            """)
            
            tables = cursor.fetchall()
            cursor.close()
            return tables
            
        except Exception as e:
            self.logger.error(f"获取表列表失败: {e}")
            return []

class ImprovedGeoServerPublisher:
    """改进的GeoServer发布器"""
    
    def __init__(self, base_url, username, password):
        self.base_url = base_url.rstrip('/')
        self.auth = (username, password)
        self.session = requests.Session()
        self.session.auth = self.auth
        self.logger = log_manager.get_logger('GeoServerPublisher')
        
    def test_connection(self):
        """测试连接"""
        try:
            self.logger.info(f"测试GeoServer连接: {self.base_url}")
            response = self.session.get(f"{self.base_url}/rest/about/version", timeout=10)
            
            if response.status_code == 200:
                self.logger.info("GeoServer连接成功")
                return True, "连接成功"
            else:
                self.logger.error(f"GeoServer连接失败: HTTP {response.status_code}")
                return False, f"HTTP {response.status_code}"
                
        except Exception as e:
            self.logger.error(f"GeoServer连接异常: {e}")
            return False, str(e)
    
    def create_workspace(self, workspace_name, namespace_uri=None):
        """创建工作空间"""
        if namespace_uri is None:
            namespace_uri = f"http://www.example.com/{workspace_name}"
        
        workspace_data = {
            "workspace": {
                "name": workspace_name,
                "namespaceURI": namespace_uri
            }
        }
        
        try:
            self.logger.info(f"创建工作空间: {workspace_name}")
            
            response = self.session.post(
                f"{self.base_url}/rest/workspaces",
                json=workspace_data,
                headers={'Content-Type': 'application/json'},
                timeout=30
            )
            
            if response.status_code in [200, 201]:
                log_manager.log_operation("创建工作空间", workspace_name, True)
                return True, "创建成功"
            elif response.status_code == 409:
                self.logger.info(f"工作空间已存在: {workspace_name}")
                return True, "工作空间已存在"
            else:
                self.logger.error(f"工作空间创建失败: {response.status_code} - {response.text}")
                return False, f"创建失败: {response.status_code}"
                
        except Exception as e:
            log_manager.log_exception("创建工作空间", e)
            return False, str(e)
    
    def create_postgresql_datastore(self, workspace, datastore_name, pg_params):
        """创建PostgreSQL数据存储"""
        datastore_data = {
            "dataStore": {
                "name": datastore_name,
                "connectionParameters": {
                    "host": pg_params['host'],
                    "port": str(pg_params['port']),
                    "database": pg_params['database'],
                    "user": pg_params['user'],
                    "passwd": pg_params['password'],
                    "dbtype": "postgis",
                    "schema": "public",
                    "Loose bbox": "true",
                    "Estimated extends": "false",
                    "validate connections": "true",
                    "Connection timeout": "20",
                    "min connections": "1",
                    "max connections": "10"
                }
            }
        }
        
        try:
            self.logger.info(f"创建数据存储: {workspace}/{datastore_name}")
            
            response = self.session.post(
                f"{self.base_url}/rest/workspaces/{workspace}/datastores",
                json=datastore_data,
                headers={'Content-Type': 'application/json'},
                timeout=30
            )
            
            if response.status_code in [200, 201]:
                log_manager.log_operation("创建数据存储", f"{workspace}/{datastore_name}", True)
                return True, "创建成功"
            elif response.status_code == 409:
                self.logger.info(f"数据存储已存在: {datastore_name}")
                return True, "数据存储已存在"
            else:
                self.logger.error(f"数据存储创建失败: {response.status_code} - {response.text}")
                return False, f"创建失败: {response.status_code}"
                
        except Exception as e:
            log_manager.log_exception("创建数据存储", e)
            return False, str(e)
    
    def publish_layer_from_table(self, workspace, datastore, table_name, layer_name=None, 
                                title=None, srs="EPSG:4326"):
        """从数据库表发布图层"""
        if layer_name is None:
            layer_name = table_name
        if title is None:
            title = layer_name
            
        featuretype_data = {
            "featureType": {
                "name": layer_name,
                "nativeName": table_name,
                "title": title,
                "srs": srs,
                "enabled": True,
                "advertised": True,
                "metadata": {
                    "entry": [
                        {"@key": "cachingEnabled", "$": "true"},
                        {"@key": "time", "$": "false"}
                    ]
                }
            }
        }
        
        try:
            self.logger.info(f"发布图层: {workspace}/{datastore}/{layer_name}")
            
            response = self.session.post(
                f"{self.base_url}/rest/workspaces/{workspace}/datastores/{datastore}/featuretypes",
                json=featuretype_data,
                headers={'Content-Type': 'application/json'},
                timeout=30
            )
            
            if response.status_code in [200, 201]:
                log_manager.log_operation("发布图层", f"{workspace}/{layer_name}", True)
                return True, "发布成功"
            else:
                self.logger.error(f"图层发布失败: {response.status_code} - {response.text}")
                return False, f"发布失败: {response.status_code}"
                
        except Exception as e:
            log_manager.log_exception("发布图层", e)
            return False, str(e)
    
    def upload_style(self, style_name, sld_content, workspace=None):
        """上传样式"""
        try:
            self.logger.info(f"上传样式: {style_name}")
            
            # 首先创建样式定义
            style_data = {
                "style": {
                    "name": style_name,
                    "filename": f"{style_name}.sld"
                }
            }
            
            if workspace:
                url = f"{self.base_url}/rest/workspaces/{workspace}/styles"
            else:
                url = f"{self.base_url}/rest/styles"
            
            response = self.session.post(
                url,
                json=style_data,
                headers={'Content-Type': 'application/json'},
                timeout=30
            )
            
            if response.status_code not in [200, 201]:
                if response.status_code != 409:  # 不是已存在错误
                    return False, f"样式创建失败: {response.status_code}"
            
            # 上传SLD内容
            if workspace:
                sld_url = f"{self.base_url}/rest/workspaces/{workspace}/styles/{style_name}"
            else:
                sld_url = f"{self.base_url}/rest/styles/{style_name}"
            
            sld_response = self.session.put(
                sld_url,
                data=sld_content,
                headers={'Content-Type': 'application/vnd.ogc.sld+xml'},
                timeout=30
            )
            
            if sld_response.status_code in [200, 201]:
                log_manager.log_operation("上传样式", style_name, True)
                return True, "上传成功"
            else:
                self.logger.error(f"SLD上传失败: {sld_response.status_code}")
                return False, f"SLD上传失败: {sld_response.status_code}"
                
        except Exception as e:
            log_manager.log_exception("上传样式", e)
            return False, str(e)
    
    def get_workspaces(self):
        """获取工作空间"""
        try:
            url = f"{self.base_url}/rest/workspaces"
            response = self.session.get(url, timeout=10)
            
            if response.status_code == 200:
                data = response.json()
                workspaces = data.get('workspaces', {})
                
                if workspaces and 'workspace' in workspaces:
                    workspace_list = workspaces['workspace']
                    if isinstance(workspace_list, dict):
                        return [workspace_list]
                    return workspace_list if isinstance(workspace_list, list) else []
                        
            return []
            
        except Exception as e:
            self.logger.error(f"获取工作空间失败: {e}")
            return []
    
    def get_datastores(self, workspace):
        """获取数据存储"""
        try:
            url = f"{self.base_url}/rest/workspaces/{workspace}/datastores"
            response = self.session.get(url, timeout=10)
            
            if response.status_code == 200:
                data = response.json()
                datastores = data.get('dataStores', {})
                
                if datastores and 'dataStore' in datastores:
                    datastore_list = datastores['dataStore']
                    if isinstance(datastore_list, dict):
                        return [datastore_list]
                    return datastore_list if isinstance(datastore_list, list) else []
                        
            return []
            
        except Exception as e:
            self.logger.error(f"获取数据存储失败: {e}")
            return []
    
    def get_layers(self, workspace):
        """获取图层"""
        try:
            url = f"{self.base_url}/rest/workspaces/{workspace}/layers"
            response = self.session.get(url, timeout=10)
            
            if response.status_code == 200:
                data = response.json()
                layers = data.get('layers', {})
                
                if layers and 'layer' in layers:
                    layer_list = layers['layer']
                    if isinstance(layer_list, dict):
                        return [layer_list]
                    return layer_list if isinstance(layer_list, list) else []
                        
            return []
            
        except Exception as e:
            self.logger.error(f"获取图层失败: {e}")
            return []
    
    def get_styles(self, workspace=None):
        """获取样式"""
        try:
            if workspace:
                url = f"{self.base_url}/rest/workspaces/{workspace}/styles"
            else:
                url = f"{self.base_url}/rest/styles"
                
            response = self.session.get(url, timeout=10)
            
            if response.status_code == 200:
                data = response.json()
                styles = data.get('styles', {})
                
                if styles and 'style' in styles:
                    style_list = styles['style']
                    if isinstance(style_list, dict):
                        return [style_list]
                    return style_list if isinstance(style_list, list) else []
                        
            return []
            
        except Exception as e:
            self.logger.error(f"获取样式失败: {e}")
            return []

class ImprovedBatchProcessor:
    """改进的批处理器"""
    
    def __init__(self, pg_params, gs_config):
        self.pg_manager = ImprovedPostgreSQLManager(pg_params)
        self.gs_publisher = ImprovedGeoServerPublisher(**gs_config)
        self.logger = log_manager.get_logger('BatchProcessor')
        
    def process_data_items(self, data_items, workspace, datastore_name, 
                          progress_callback=None, status_callback=None):
        """批量处理数据项"""
        
        try:
            # 连接数据库
            success, message = self.pg_manager.connect()
            if not success:
                return False, f"数据库连接失败: {message}"
            
            # 检查GeoServer连接
            success, message = self.gs_publisher.test_connection()
            if not success:
                return False, f"GeoServer连接失败: {message}"
            
            # 创建工作空间
            success, message = self.gs_publisher.create_workspace(workspace)
            if not success:
                return False, f"工作空间创建失败: {message}"
            
            # 创建数据存储
            success, message = self.gs_publisher.create_postgresql_datastore(
                workspace, datastore_name, self.pg_manager.params
            )
            if not success:
                return False, f"数据存储创建失败: {message}"
            
            total_items = len(data_items)
            success_count = 0
            error_count = 0
            
            self.logger.info(f"开始批处理 {total_items} 个数据项")
            
            for i, item in enumerate(data_items):
                try:
                    if progress_callback:
                        progress_callback(int((i / total_items) * 100))
                    
                    if status_callback:
                        status_callback(f"正在处理: {item['new_name']}")
                    
                    # 导入到PostgreSQL
                    import_success = self._import_single_item(item)
                    
                    if import_success:
                        # 发布到GeoServer
                        publish_success = self._publish_single_item(
                            item, workspace, datastore_name
                        )
                        
                        if publish_success:
                            success_count += 1
                            self.logger.info(f"处理成功: {item['new_name']}")
                        else:
                            error_count += 1
                            self.logger.error(f"发布失败: {item['new_name']}")
                    else:
                        error_count += 1
                        self.logger.error(f"导入失败: {item['new_name']}")
                        
                except Exception as e:
                    error_count += 1
                    log_manager.log_exception(f"处理数据项 {item['new_name']}", e)
            
            if progress_callback:
                progress_callback(100)
            
            if status_callback:
                status_callback(f"处理完成: 成功 {success_count}, 失败 {error_count}")
            
            log_manager.log_operation(
                "批量处理数据", 
                f"总计 {total_items}, 成功 {success_count}, 失败 {error_count}",
                success_count > 0
            )
            
            return success_count > 0, f"处理完成: 成功 {success_count}/{total_items} 个"
            
        except Exception as e:
            log_manager.log_exception("批量处理数据", e)
            return False, str(e)
    
    def _import_single_item(self, item):
        """导入单个数据项"""
        try:
            file_path = item['path']
            table_name = item['new_name']
            data_type = item['type']
            
            # 检测SRID
            srid_text = item.get('srs', 'EPSG:4326')
            target_crs = srid_text if srid_text.startswith('EPSG:') else 'EPSG:4326'
            
            if data_type == "矢量数据":
                success, message = self.pg_manager.import_vector_file(
                    file_path, table_name, target_crs=target_crs
                )
                return success
                
            elif data_type == "栅格数据":
                success, message = self.pg_manager.import_raster_file(
                    file_path, table_name, target_crs=target_crs
                )
                return success
                
            elif data_type == "空间表":
                # 已经在数据库中，跳过导入
                return True
            else:
                self.logger.warning(f"未知数据类型: {data_type}")
                return False
                
        except Exception as e:
            log_manager.log_exception(f"导入数据项 {item['new_name']}", e)
            return False
    
    def _publish_single_item(self, item, workspace, datastore_name):
        """发布单个数据项"""
        try:
            table_name = item['new_name']
            layer_name = item['new_name']
            srid_text = item.get('srs', 'EPSG:4326')
            
            # 发布图层
            success, message = self.gs_publisher.publish_layer_from_table(
                workspace, datastore_name, table_name, layer_name, srs=srid_text
            )
            
            return success
            
        except Exception as e:
            log_manager.log_exception(f"发布数据项 {item['new_name']}", e)
            return False

# ================== GUI界面部分 ==================

def get_icon(name):
    """获取图标，使用文字代替图标"""
    icons = {
        'server': '🌍',
        'database': '🗄️',
        'import': '📥',
        'style': '🎨',
        'layers': '📋',
        'connect': '🔌',
        'refresh': '🔄',
        'folder': '📁',
        'file': '📄',
        'map': '🗺️',
        'table': '📋',
        'spatial': '🌐',
        'success': '✅',
        'error': '❌',
        'warning': '⚠️',
        'loading': '⏳',
        'log': '📝'
    }
    return icons.get(name, '📄')

class ImprovedDataScanner:
    """改进的数据扫描器"""
    
    def __init__(self):
        self.logger = log_manager.get_logger('DataScanner')
        if HAS_SPATIAL_LIBS:
            self.processor = ImprovedSpatialDataProcessor()
        else:
            self.processor = None
    
    def scan_folder(self, folder_path):
        """扫描文件夹中的空间数据"""
        if not self.processor:
            raise ImportError("缺少空间数据处理库")
            
        vector_extensions = {'.shp', '.geojson', '.kml', '.gpkg', '.gml'}
        raster_extensions = {'.tif', '.tiff', '.img', '.jp2', '.png', '.jpg'}
        
        found_data = []
        
        try:
            self.logger.info(f"开始扫描文件夹: {folder_path}")
            
            for root, dirs, files in os.walk(folder_path):
                for file in files:
                    file_path = os.path.join(root, file)
                    file_ext = Path(file).suffix.lower()
                    
                    if file_ext in vector_extensions or file_ext in raster_extensions:
                        try:
                            # 获取详细文件信息
                            file_info = self.processor.get_file_info(file_path)
                            
                            if file_info:
                                data_item = {
                                    'original_name': file,
                                    'path': file_path,
                                    'type': file_info['type'],
                                    'size': file_info['size_formatted'],
                                    'srs': file_info.get('crs', 'EPSG:4326'),
                                    'new_name': self.normalize_name(Path(file).stem),
                                    'style': 'default',
                                    'geometry_type': file_info.get('geometry_type'),
                                    'feature_count': file_info.get('feature_count'),
                                    'extent': file_info.get('extent')
                                }
                                found_data.append(data_item)
                                
                        except Exception as e:
                            self.logger.warning(f"处理文件失败 {file_path}: {e}")
                            
            self.logger.info(f"扫描完成，找到 {len(found_data)} 个空间数据文件")
            
        except Exception as e:
            log_manager.log_exception("扫描文件夹", e)
            
        return found_data
    
    @staticmethod
    def normalize_name(name):
        """规范化名称"""
        # 转换为小写，替换空格和特殊字符为下划线
        normalized = re.sub(r'[^a-z0-9_]', '_', name.lower())
        # 移除多余的下划线
        normalized = re.sub(r'_+', '_', normalized)
        # 移除开头和结尾的下划线
        normalized = normalized.strip('_')
        
        if not normalized:
            normalized = 'unnamed'
            
        return normalized

class WorkerThread(QThread):
    """工作线程"""
    progress = pyqtSignal(int)
    status = pyqtSignal(str)
    finished = pyqtSignal(bool, str)
    
    def __init__(self, task_func, *args, **kwargs):
        super().__init__()
        self.task_func = task_func
        self.args = args
        self.kwargs = kwargs
        self.logger = log_manager.get_logger('WorkerThread')
        
    def run(self):
        try:
            self.logger.debug("开始执行工作线程任务")
            result = self.task_func(*self.args, **self.kwargs)
            if isinstance(result, tuple):
                success, message = result
                self.finished.emit(success, message)
            else:
                self.finished.emit(True, "操作完成")
        except Exception as e:
            log_manager.log_exception("工作线程任务", e)
            self.finished.emit(False, f"操作失败: {str(e)}")

class LogViewDialog(QDialog):
    """日志查看对话框"""
    
    def __init__(self, parent=None):
        super().__init__(parent)
        self.setWindowTitle(f"{get_icon('log')} 日志查看器")
        self.setModal(False)
        self.resize(800, 600)
        
        layout = QVBoxLayout()
        
        # 工具栏
        toolbar_layout = QHBoxLayout()
        
        self.refresh_btn = QPushButton(f"{get_icon('refresh')} 刷新")
        self.refresh_btn.clicked.connect(self.refresh_logs)
        
        self.clear_btn = QPushButton("🗑️ 清空")
        self.clear_btn.clicked.connect(self.clear_logs)
        
        self.export_btn = QPushButton("💾 导出")
        self.export_btn.clicked.connect(self.export_logs)
        
        toolbar_layout.addWidget(self.refresh_btn)
        toolbar_layout.addWidget(self.clear_btn)
        toolbar_layout.addWidget(self.export_btn)
        toolbar_layout.addStretch()
        
        layout.addLayout(toolbar_layout)
        
        # 日志显示
        self.log_text = QTextEdit()
        self.log_text.setReadOnly(True)
        self.log_text.setFont(QFont("Consolas", 9))
        layout.addWidget(self.log_text)
        
        # 关闭按钮
        self.close_btn = QPushButton("关闭")
        self.close_btn.clicked.connect(self.close)
        layout.addWidget(self.close_btn)
        
        self.setLayout(layout)
        
        # 加载日志
        self.refresh_logs()
    
    def refresh_logs(self):
        """刷新日志"""
        try:
            log_file = log_manager.log_dir / 'application.log'
            if log_file.exists():
                with open(log_file, 'r', encoding='utf-8') as f:
                    # 读取最后1000行
                    lines = f.readlines()
                    recent_lines = lines[-1000:] if len(lines) > 1000 else lines
                    self.log_text.setPlainText(''.join(recent_lines))
                    
                # 滚动到底部
                scrollbar = self.log_text.verticalScrollBar()
                scrollbar.setValue(scrollbar.maximum())
        except Exception as e:
            self.log_text.setPlainText(f"无法读取日志文件: {e}")
    
    def clear_logs(self):
        """清空日志显示"""
        self.log_text.clear()
    
    def export_logs(self):
        """导出日志"""
        try:
            file_path, _ = QFileDialog.getSaveFileName(
                self, "导出日志", 
                f"logs_export_{datetime.now().strftime('%Y%m%d_%H%M%S')}.txt",
                "文本文件 (*.txt);;所有文件 (*.*)"
            )
            
            if file_path:
                with open(file_path, 'w', encoding='utf-8') as f:
                    f.write(self.log_text.toPlainText())
                QMessageBox.information(self, "成功", f"日志已导出到: {file_path}")
                
        except Exception as e:
            QMessageBox.critical(self, "错误", f"导出日志失败: {e}")

class DatabaseConnection:
    """数据库连接管理类"""
    
    def __init__(self):
        self.connection = None
        self.params = {}
        self.logger = log_manager.get_logger('DatabaseConnection')
        
    def test_connection(self, host, port, database, username, password):
        """测试数据库连接"""
        try:
            self.params = {
                'host': host,
                'port': int(port),
                'database': database,
                'user': username,
                'password': password
            }
            
            self.logger.info(f"测试数据库连接: {host}:{port}/{database}")
            
            conn = psycopg2.connect(**self.params)
            
            # 检查PostGIS扩展
            cursor = conn.cursor()
            cursor.execute("SELECT EXISTS(SELECT 1 FROM pg_extension WHERE extname='postgis')")
            has_postgis = cursor.fetchone()[0]
            cursor.close()
            
            if has_postgis:
                self.connection = conn
                log_manager.log_operation("数据库连接测试", f"{host}:{port}/{database}", True)
                return True, "连接成功，PostGIS扩展已安装"
            else:
                conn.close()
                return False, "连接成功，但未安装PostGIS扩展"
                
        except Exception as e:
            log_manager.log_exception("数据库连接测试", e)
            return False, f"连接失败: {str(e)}"
    
    def get_spatial_tables(self):
        """获取空间数据表"""
        if not self.connection:
            return []
            
        try:
            pg_manager = ImprovedPostgreSQLManager(self.params)
            pg_manager.connection = self.connection
            return pg_manager.get_spatial_tables()
            
        except Exception as e:
            self.logger.error(f"获取空间表失败: {e}")
            return []
    
    def get_all_tables(self):
        """获取所有数据表"""
        if not self.connection:
            return []
            
        try:
            pg_manager = ImprovedPostgreSQLManager(self.params)
            pg_manager.connection = self.connection
            return pg_manager.get_all_tables()
            
        except Exception as e:
            self.logger.error(f"获取表列表失败: {e}")
            return []

class GeoServerConnection:
    """GeoServer连接管理类"""
    
    def __init__(self):
        self.base_url = ""
        self.username = ""
        self.password = ""
        self.auth = None
        self.connected = False
        self.logger = log_manager.get_logger('GeoServerConnection')
        
    def test_connection(self, url, username, password):
        """测试GeoServer连接"""
        try:
            self.base_url = url.rstrip('/')
            self.username = username
            self.password = password
            self.auth = (username, password)
            
            self.logger.info(f"测试GeoServer连接: {url}")
            
            test_url = f"{self.base_url}/rest/about/version"
            response = requests.get(test_url, auth=self.auth, timeout=10)
            
            if response.status_code == 200:
                self.connected = True
                log_manager.log_operation("GeoServer连接测试", url, True)
                return True, "GeoServer连接成功"
            else:
                return False, f"连接失败: HTTP {response.status_code}"
                
        except Exception as e:
            log_manager.log_exception("GeoServer连接测试", e)
            return False, f"连接异常: {str(e)}"
    
    def get_workspaces(self):
        """获取工作空间"""
        if not self.connected:
            return []
            
        try:
            publisher = ImprovedGeoServerPublisher(self.base_url, self.username, self.password)
            return publisher.get_workspaces()
            
        except Exception as e:
            self.logger.error(f"获取工作空间失败: {e}")
            return []
    
    def get_datastores(self, workspace):
        """获取数据存储"""
        try:
            publisher = ImprovedGeoServerPublisher(self.base_url, self.username, self.password)
            return publisher.get_datastores(workspace)
            
        except Exception as e:
            self.logger.error(f"获取数据存储失败: {e}")
            return []
    
    def get_layers(self, workspace):
        """获取图层"""
        try:
            publisher = ImprovedGeoServerPublisher(self.base_url, self.username, self.password)
            return publisher.get_layers(workspace)
            
        except Exception as e:
            self.logger.error(f"获取图层失败: {e}")
            return []
    
    def get_styles(self, workspace=None):
        """获取样式"""
        try:
            publisher = ImprovedGeoServerPublisher(self.base_url, self.username, self.password)
            return publisher.get_styles(workspace)
            
        except Exception as e:
            self.logger.error(f"获取样式失败: {e}")
            return []

class StyleDialog(QDialog):
    """样式选择对话框"""
    
    def __init__(self, available_styles, parent=None):
        super().__init__(parent)
        self.setWindowTitle("选择样式")
        self.setModal(True)
        self.resize(400, 300)
        
        layout = QVBoxLayout()
        
        # 样式列表
        self.style_list = QListWidget()
        self.style_list.addItem("default")
        
        for style in available_styles:
            style_name = style.get('name', 'unknown')
            self.style_list.addItem(style_name)
            
        layout.addWidget(QLabel("选择样式:"))
        layout.addWidget(self.style_list)
        
        # 按钮
        buttons = QDialogButtonBox(QDialogButtonBox.StandardButton.Ok | QDialogButtonBox.StandardButton.Cancel)
        buttons.accepted.connect(self.accept)
        buttons.rejected.connect(self.reject)
        layout.addWidget(buttons)
        
        self.setLayout(layout)
        
    def get_selected_style(self):
        current_item = self.style_list.currentItem()
        return current_item.text() if current_item else "default"

class TableRenameDialog(QDialog):
    """表重命名对话框"""
    
    def __init__(self, current_name, parent=None):
        super().__init__(parent)
        self.setWindowTitle("重命名表")
        self.setModal(True)
        self.resize(400, 150)
        
        layout = QVBoxLayout()
        
        # 当前名称
        layout.addWidget(QLabel(f"当前表名: {current_name}"))
        
        # 新名称输入
        self.new_name_edit = QLineEdit(current_name)
        layout.addWidget(QLabel("新表名:"))
        layout.addWidget(self.new_name_edit)
        
        # 按钮
        buttons = QDialogButtonBox(QDialogButtonBox.StandardButton.Ok | QDialogButtonBox.StandardButton.Cancel)
        buttons.accepted.connect(self.accept)
        buttons.rejected.connect(self.reject)
        layout.addWidget(buttons)
        
        self.setLayout(layout)
        
    def get_new_name(self):
        return self.new_name_edit.text().strip()

class ImprovedMainWindow(QMainWindow):
    """改进的主窗口"""
    
    def __init__(self):
        super().__init__()
        self.setWindowTitle("GeoServer & PostgreSQL 数据管理系统 V2.1")
        self.setGeometry(100, 100, 1400, 900)
        
        self.logger = log_manager.get_logger('MainWindow')
        
        # 连接管理器
        self.db_connection = DatabaseConnection()
        self.gs_connection = GeoServerConnection()
        
        # 数据存储
        self.scanned_data = []
        self.available_styles = []
        
        # 检查依赖
        self.check_dependencies()
        
        self.setup_ui()
        self.setup_style()
        
        self.logger.info("主窗口初始化完成")
        
    def check_dependencies(self):
        """检查依赖库"""
        if not HAS_SPATIAL_LIBS:
            QMessageBox.warning(self, "缺少依赖库", 
                "缺少空间数据处理库，某些功能可能无法使用。\n\n"
                "请安装以下库:\n"
                "pip install geopandas fiona rasterio\n\n"
                "注意：在Windows上可能需要先安装GDAL")
    
    def setup_style(self):
        """设置样式"""
        self.setStyleSheet("""
            QMainWindow {
                background-color: #f0f0f0;
            }
            QTabWidget::pane {
                border: 1px solid #c0c0c0;
                background-color: white;
            }
            QTabBar::tab {
                padding: 8px 16px;
                margin: 2px;
            }
            QTabBar::tab:selected {
                background-color: #4CAF50;
                color: white;
            }
            QGroupBox {
                font-weight: bold;
                border: 2px solid #cccccc;
                border-radius: 5px;
                margin: 5px 0px;
                padding-top: 10px;
            }
            QGroupBox::title {
                subcontrol-origin: margin;
                left: 10px;
                padding: 0 5px 0 5px;
            }
            QPushButton {
                padding: 6px 12px;
                border: 1px solid #ccc;
                border-radius: 4px;
                background-color: #f8f9fa;
            }
            QPushButton:hover {
                background-color: #e9ecef;
            }
            QPushButton:pressed {
                background-color: #dee2e6;
            }
            QLineEdit, QComboBox {
                padding: 4px;
                border: 1px solid #ccc;
                border-radius: 4px;
            }
            QTreeWidget, QTableWidget {
                border: 1px solid #ccc;
                alternate-background-color: #f9f9f9;
            }
            QProgressBar {
                border: 1px solid #ccc;
                border-radius: 4px;
                text-align: center;
            }
            QProgressBar::chunk {
                background-color: #4CAF50;
                border-radius: 3px;
            }
        """)
        
    def setup_ui(self):
        """设置用户界面"""
        central_widget = QWidget()
        self.setCentralWidget(central_widget)
        
        layout = QVBoxLayout()
        central_widget.setLayout(layout)
        
        # 顶部工具栏
        self.setup_toolbar(layout)
        
        # 创建选项卡
        self.tab_widget = QTabWidget()
        layout.addWidget(self.tab_widget)
        
        # 各个选项卡
        self.setup_geoserver_tab()
        self.setup_postgresql_tab()
        self.setup_import_tab()
        self.setup_style_tab()
        self.setup_layers_tab()
        
        # 状态栏
        self.statusBar().showMessage("就绪")
        
    def setup_toolbar(self, layout):
        """设置工具栏"""
        toolbar_layout = QHBoxLayout()
        
        # 日志按钮
        self.log_btn = QPushButton(f"{get_icon('log')} 查看日志")
        self.log_btn.clicked.connect(self.show_log_dialog)
        toolbar_layout.addWidget(self.log_btn)
        
        # 刷新按钮
        self.global_refresh_btn = QPushButton(f"{get_icon('refresh')} 全局刷新")
        self.global_refresh_btn.clicked.connect(self.global_refresh)
        toolbar_layout.addWidget(self.global_refresh_btn)
        
        # 状态指示器
        self.connection_status = QLabel("🔴 未连接")
        toolbar_layout.addWidget(self.connection_status)
        
        toolbar_layout.addStretch()
        layout.addLayout(toolbar_layout)
    
    def show_log_dialog(self):
        """显示日志对话框"""
        dialog = LogViewDialog(self)
        dialog.show()
    
    def global_refresh(self):
        """全局刷新"""
        try:
            if self.gs_connection.connected:
                self.refresh_geoserver_info()
                self.refresh_workspaces()
                self.refresh_styles()
                self.refresh_published_layers()
            
            if self.db_connection.connection:
                self.refresh_postgresql_info()
            
            QMessageBox.information(self, "完成", "全局刷新完成")
            
        except Exception as e:
            log_manager.log_exception("全局刷新", e)
            QMessageBox.critical(self, "错误", f"全局刷新失败: {e}")
    
    def update_connection_status(self):
        """更新连接状态"""
        gs_status = "🟢" if self.gs_connection.connected else "🔴"
        pg_status = "🟢" if self.db_connection.connection else "🔴"
        
        self.connection_status.setText(f"{gs_status} GeoServer | {pg_status} PostgreSQL")
    
    def setup_geoserver_tab(self):
        """设置GeoServer选项卡"""
        widget = QWidget()
        layout = QVBoxLayout(widget)
        
        # 连接设置
        connection_group = QGroupBox(f"{get_icon('server')} GeoServer连接设置")
        connection_layout = QFormLayout()
        
        self.gs_url_edit = QLineEdit("http://localhost:8080/geoserver")
        self.gs_username_edit = QLineEdit("admin")
        self.gs_password_edit = QLineEdit("geoserver")
        self.gs_password_edit.setEchoMode(QLineEdit.EchoMode.Password)
        
        connection_layout.addRow("服务器URL:", self.gs_url_edit)
        connection_layout.addRow("用户名:", self.gs_username_edit)
        connection_layout.addRow("密码:", self.gs_password_edit)
        
        self.gs_connect_btn = QPushButton(f"{get_icon('connect')} 测试连接")
        self.gs_connect_btn.clicked.connect(self.test_geoserver_connection)
        connection_layout.addRow(self.gs_connect_btn)
        
        self.gs_status_label = QLabel(f"{get_icon('error')} 未连接")
        connection_layout.addRow("状态:", self.gs_status_label)
        
        connection_group.setLayout(connection_layout)
        layout.addWidget(connection_group)
        
        # 信息展示
        info_group = QGroupBox(f"{get_icon('server')} GeoServer信息")
        info_layout = QVBoxLayout()
        
        # 刷新按钮
        self.gs_refresh_btn = QPushButton(f"{get_icon('refresh')} 刷新信息")
        self.gs_refresh_btn.clicked.connect(self.refresh_geoserver_info)
        self.gs_refresh_btn.setEnabled(False)
        info_layout.addWidget(self.gs_refresh_btn)
        
        # 信息树
        self.gs_tree = QTreeWidget()
        self.gs_tree.setHeaderLabels(["项目", "类型", "名称"])
        info_layout.addWidget(self.gs_tree)
        
        info_group.setLayout(info_layout)
        layout.addWidget(info_group)
        
        self.tab_widget.addTab(widget, f"{get_icon('server')} GeoServer管理")
        
    def setup_postgresql_tab(self):
        """设置PostgreSQL选项卡"""
        widget = QWidget()
        layout = QVBoxLayout(widget)
        
        # 连接设置
        connection_group = QGroupBox(f"{get_icon('database')} PostgreSQL连接设置")
        connection_layout = QFormLayout()
        
        self.pg_host_edit = QLineEdit("localhost")
        self.pg_port_edit = QLineEdit("5432")
        self.pg_username_edit = QLineEdit("postgres")
        self.pg_password_edit = QLineEdit("")
        self.pg_password_edit.setEchoMode(QLineEdit.EchoMode.Password)
        self.pg_database_edit = QLineEdit("postgres")
        
        connection_layout.addRow("主机:", self.pg_host_edit)
        connection_layout.addRow("端口:", self.pg_port_edit)
        connection_layout.addRow("用户名:", self.pg_username_edit)
        connection_layout.addRow("密码:", self.pg_password_edit)
        connection_layout.addRow("数据库:", self.pg_database_edit)
        
        self.pg_connect_btn = QPushButton(f"{get_icon('connect')} 测试连接")
        self.pg_connect_btn.clicked.connect(self.test_postgresql_connection)
        connection_layout.addRow(self.pg_connect_btn)
        
        self.pg_status_label = QLabel(f"{get_icon('error')} 未连接")
        connection_layout.addRow("状态:", self.pg_status_label)
        
        connection_group.setLayout(connection_layout)
        layout.addWidget(connection_group)
        
        # 数据库信息
        info_group = QGroupBox(f"{get_icon('database')} 数据库信息")
        info_layout = QVBoxLayout()
        
        # 操作按钮布局
        button_layout = QHBoxLayout()
        
        self.pg_refresh_btn = QPushButton(f"{get_icon('refresh')} 刷新数据库")
        self.pg_refresh_btn.clicked.connect(self.refresh_postgresql_info)
        self.pg_refresh_btn.setEnabled(False)
        button_layout.addWidget(self.pg_refresh_btn)
        
        self.pg_rename_btn = QPushButton("✏️ 重命名表")
        self.pg_rename_btn.clicked.connect(self.rename_table)
        self.pg_rename_btn.setEnabled(False)
        button_layout.addWidget(self.pg_rename_btn)
        
        button_layout.addStretch()
        info_layout.addLayout(button_layout)
        
        # 数据库树
        self.pg_tree = QTreeWidget()
        self.pg_tree.setHeaderLabels(["名称", "类型", "模式", "几何类型", "大小"])
        self.pg_tree.itemSelectionChanged.connect(self.on_table_selected)
        info_layout.addWidget(self.pg_tree)
        
        info_group.setLayout(info_layout)
        layout.addWidget(info_group)
        
        self.tab_widget.addTab(widget, f"{get_icon('database')} PostgreSQL管理")
        
    def setup_import_tab(self):
        """设置数据导入选项卡"""
        widget = QWidget()
        layout = QVBoxLayout(widget)
        
        # 数据源选择
        source_group = QGroupBox(f"{get_icon('import')} 数据源选择")
        source_layout = QVBoxLayout()
        
        # 导入类型
        type_layout = QHBoxLayout()
        self.import_type_group = QButtonGroup()
        
        self.folder_radio = QRadioButton(f"{get_icon('folder')} 文件夹扫描")
        self.folder_radio.setChecked(True)
        self.pg_radio = QRadioButton(f"{get_icon('database')} PostgreSQL数据库")
        
        self.import_type_group.addButton(self.folder_radio, 0)
        self.import_type_group.addButton(self.pg_radio, 1)
        
        type_layout.addWidget(self.folder_radio)
        type_layout.addWidget(self.pg_radio)
        type_layout.addStretch()
        
        source_layout.addLayout(type_layout)
        
        # 路径选择
        path_layout = QHBoxLayout()
        self.source_path_edit = QLineEdit()
        self.browse_btn = QPushButton(f"{get_icon('folder')} 浏览")
        self.browse_btn.clicked.connect(self.browse_source)
        
        path_layout.addWidget(QLabel("数据源:"))
        path_layout.addWidget(self.source_path_edit)
        path_layout.addWidget(self.browse_btn)
        
        source_layout.addLayout(path_layout)
        
        # 扫描按钮
        self.scan_btn = QPushButton(f"{get_icon('refresh')} 扫描数据")
        self.scan_btn.clicked.connect(self.scan_data)
        source_layout.addWidget(self.scan_btn)
        
        source_group.setLayout(source_layout)
        layout.addWidget(source_group)
        
        # 扫描结果
        result_group = QGroupBox(f"{get_icon('file')} 扫描结果")
        result_layout = QVBoxLayout()
        
        # 数据表格
        self.data_table = QTableWidget()
        self.data_table.setColumnCount(7)
        self.data_table.setHorizontalHeaderLabels([
            "原始名称", "数据类型", "大小", "坐标系", "新名称", "样式", "要素数量"
        ])
        self.data_table.horizontalHeader().setStretchLastSection(True)
        self.data_table.cellChanged.connect(self.on_cell_changed)
        result_layout.addWidget(self.data_table)
        
        # 批量操作按钮
        batch_layout = QHBoxLayout()
        
        self.batch_rename_btn = QPushButton("✏️ 批量重命名")
        self.batch_rename_btn.clicked.connect(self.batch_rename)
        
        self.batch_style_btn = QPushButton(f"{get_icon('style')} 批量设置样式")
        self.batch_style_btn.clicked.connect(self.batch_set_style)
        
        batch_layout.addWidget(self.batch_rename_btn)
        batch_layout.addWidget(self.batch_style_btn)
        batch_layout.addStretch()
        
        result_layout.addLayout(batch_layout)
        result_group.setLayout(result_layout)
        layout.addWidget(result_group)
        
        # 工作空间设置
        workspace_group = QGroupBox("工作空间设置")
        workspace_layout = QHBoxLayout()
        
        self.workspace_combo = QComboBox()
        self.workspace_combo.setEditable(True)
        
        self.refresh_workspace_btn = QPushButton(f"{get_icon('refresh')} 刷新")
        self.refresh_workspace_btn.clicked.connect(self.refresh_workspaces)
        
        workspace_layout.addWidget(QLabel("工作空间:"))
        workspace_layout.addWidget(self.workspace_combo)
        workspace_layout.addWidget(self.refresh_workspace_btn)
        workspace_layout.addStretch()
        
        workspace_group.setLayout(workspace_layout)
        layout.addWidget(workspace_group)
        
        # 操作按钮
        action_layout = QHBoxLayout()
        
        self.import_pg_btn = QPushButton(f"{get_icon('database')} 导入到PostgreSQL")
        self.import_pg_btn.clicked.connect(self.import_to_postgresql)
        
        self.publish_gs_btn = QPushButton(f"{get_icon('server')} 发布到GeoServer")
        self.publish_gs_btn.clicked.connect(self.publish_to_geoserver)
        
        self.import_publish_btn = QPushButton(f"{get_icon('success')} 一键导入发布")
        self.import_publish_btn.clicked.connect(self.import_and_publish)
        
        action_layout.addWidget(self.import_pg_btn)
        action_layout.addWidget(self.publish_gs_btn)
        action_layout.addWidget(self.import_publish_btn)
        action_layout.addStretch()
        
        layout.addLayout(action_layout)
        
        # 进度条
        self.progress_bar = QProgressBar()
        layout.addWidget(self.progress_bar)
        
        # 状态标签
        self.status_label = QLabel("就绪")
        layout.addWidget(self.status_label)
        
        self.tab_widget.addTab(widget, f"{get_icon('import')} 数据导入")
        
    def setup_style_tab(self):
        """设置样式管理选项卡"""
        widget = QWidget()
        layout = QVBoxLayout(widget)
        
        # 样式导入
        import_group = QGroupBox(f"{get_icon('style')} 样式导入")
        import_layout = QFormLayout()
        
        self.sld_path_edit = QLineEdit()
        self.sld_browse_btn = QPushButton(f"{get_icon('folder')} 浏览")
        self.sld_browse_btn.clicked.connect(self.browse_sld_file)
        
        path_layout = QHBoxLayout()
        path_layout.addWidget(self.sld_path_edit)
        path_layout.addWidget(self.sld_browse_btn)
        
        self.style_name_edit = QLineEdit()
        self.style_workspace_combo = QComboBox()
        self.style_workspace_combo.setEditable(True)
        
        import_layout.addRow("SLD文件:", path_layout)
        import_layout.addRow("样式名称:", self.style_name_edit)
        import_layout.addRow("工作空间:", self.style_workspace_combo)
        
        self.import_style_btn = QPushButton(f"{get_icon('import')} 导入样式")
        self.import_style_btn.clicked.connect(self.import_style)
        import_layout.addRow(self.import_style_btn)
        
        import_group.setLayout(import_layout)
        layout.addWidget(import_group)
        
        # 样式列表
        list_group = QGroupBox(f"{get_icon('style')} 已有样式")
        list_layout = QVBoxLayout()
        
        self.refresh_styles_btn = QPushButton(f"{get_icon('refresh')} 刷新样式")
        self.refresh_styles_btn.clicked.connect(self.refresh_styles)
        list_layout.addWidget(self.refresh_styles_btn)
        
        self.style_tree = QTreeWidget()
        self.style_tree.setHeaderLabels(["样式名称", "工作空间", "文件名"])
        list_layout.addWidget(self.style_tree)
        
        list_group.setLayout(list_layout)
        layout.addWidget(list_group)
        
        self.tab_widget.addTab(widget, f"{get_icon('style')} 样式管理")
        
    def setup_layers_tab(self):
        """设置图层管理选项卡"""
        widget = QWidget()
        layout = QVBoxLayout(widget)
        
        # 筛选控件
        filter_group = QGroupBox("图层筛选")
        filter_layout = QHBoxLayout()
        
        self.workspace_filter_combo = QComboBox()
        self.layer_name_filter_edit = QLineEdit()
        
        self.filter_btn = QPushButton(f"{get_icon('refresh')} 筛选")
        self.filter_btn.clicked.connect(self.filter_layers)
        
        self.refresh_layers_btn = QPushButton(f"{get_icon('refresh')} 刷新")
        self.refresh_layers_btn.clicked.connect(self.refresh_published_layers)
        
        filter_layout.addWidget(QLabel("工作空间:"))
        filter_layout.addWidget(self.workspace_filter_combo)
        filter_layout.addWidget(QLabel("图层名称:"))
        filter_layout.addWidget(self.layer_name_filter_edit)
        filter_layout.addWidget(self.filter_btn)
        filter_layout.addWidget(self.refresh_layers_btn)
        filter_layout.addStretch()
        
        filter_group.setLayout(filter_layout)
        layout.addWidget(filter_group)
        
        # 图层列表
        layers_group = QGroupBox(f"{get_icon('layers')} 已发布图层")
        layers_layout = QVBoxLayout()
        
        self.layers_table = QTableWidget()
        self.layers_table.setColumnCount(5)
        self.layers_table.setHorizontalHeaderLabels([
            "图层名称", "工作空间", "样式", "数据源", "发布日期"
        ])
        self.layers_table.horizontalHeader().setStretchLastSection(True)
        layers_layout.addWidget(self.layers_table)
        
        layers_group.setLayout(layers_layout)
        layout.addWidget(layers_group)
        
        self.tab_widget.addTab(widget, f"{get_icon('layers')} 图层管理")
    
    def test_geoserver_connection(self):
        """测试GeoServer连接"""
        try:
            url = self.gs_url_edit.text().strip()
            username = self.gs_username_edit.text().strip()
            password = self.gs_password_edit.text().strip()
            
            if not all([url, username, password]):
                QMessageBox.warning(self, "警告", "请填写完整的连接信息")
                return
                
            success, message = self.gs_connection.test_connection(url, username, password)
            
            if success:
                self.gs_status_label.setText(f"{get_icon('success')} {message}")
                self.gs_refresh_btn.setEnabled(True)
                self.update_connection_status()
                QMessageBox.information(self, "成功", message)
                self.refresh_geoserver_info()
                self.refresh_workspaces()
                self.refresh_styles()
            else:
                self.gs_status_label.setText(f"{get_icon('error')} {message}")
                QMessageBox.critical(self, "错误", message)
                
        except Exception as e:
            log_manager.log_exception("测试GeoServer连接", e)
            QMessageBox.critical(self, "错误", f"连接测试失败: {e}")
    
    def test_postgresql_connection(self):
        """测试PostgreSQL连接"""
        try:
            host = self.pg_host_edit.text().strip()
            port = self.pg_port_edit.text().strip()
            username = self.pg_username_edit.text().strip()
            password = self.pg_password_edit.text().strip()
            database = self.pg_database_edit.text().strip()
            
            if not all([host, port, username, database]):
                QMessageBox.warning(self, "警告", "请填写完整的连接信息")
                return
                
            success, message = self.db_connection.test_connection(
                host, port, database, username, password
            )
            
            if success:
                self.pg_status_label.setText(f"{get_icon('success')} {message}")
                self.pg_refresh_btn.setEnabled(True)
                self.update_connection_status()
                QMessageBox.information(self, "成功", message)
                self.refresh_postgresql_info()
            else:
                self.pg_status_label.setText(f"{get_icon('error')} {message}")
                QMessageBox.critical(self, "错误", message)
                
        except Exception as e:
            log_manager.log_exception("测试PostgreSQL连接", e)
            QMessageBox.critical(self, "错误", f"连接测试失败: {e}")
    
    def refresh_geoserver_info(self):
        """刷新GeoServer信息"""
        if not self.gs_connection.connected:
            return
            
        try:
            self.gs_tree.clear()
            
            workspaces = self.gs_connection.get_workspaces()
            
            for workspace in workspaces:
                ws_name = workspace.get('name', 'unknown')
                ws_item = QTreeWidgetItem(self.gs_tree)
                ws_item.setText(0, f"{get_icon('folder')} {ws_name}")
                ws_item.setText(1, "工作空间")
                ws_item.setText(2, ws_name)
                
                # 获取数据存储
                datastores = self.gs_connection.get_datastores(ws_name)
                for datastore in datastores:
                    ds_name = datastore.get('name', 'unknown')
                    ds_item = QTreeWidgetItem(ws_item)
                    ds_item.setText(0, f"{get_icon('database')} {ds_name}")
                    ds_item.setText(1, "数据存储")
                    ds_item.setText(2, ds_name)
                
                # 获取图层
                layers = self.gs_connection.get_layers(ws_name)
                for layer in layers:
                    layer_name = layer.get('name', 'unknown')
                    layer_item = QTreeWidgetItem(ws_item)
                    layer_item.setText(0, f"{get_icon('map')} {layer_name}")
                    layer_item.setText(1, "图层")
                    layer_item.setText(2, layer_name)
                    
            self.gs_tree.expandAll()
            
        except Exception as e:
            log_manager.log_exception("刷新GeoServer信息", e)
            QMessageBox.critical(self, "错误", f"刷新GeoServer信息失败: {str(e)}")
    
    def refresh_postgresql_info(self):
        """刷新PostgreSQL信息"""
        if not self.db_connection.connection:
            return
            
        try:
            self.pg_tree.clear()
            
            # 获取当前数据库信息
            db_name = self.db_connection.params['database']
            db_item = QTreeWidgetItem(self.pg_tree)
            db_item.setText(0, f"{get_icon('database')} {db_name}")
            db_item.setText(1, "数据库")
            
            # 获取所有表
            tables = self.db_connection.get_all_tables()
            schemas = {}
            
            # 按模式分组
            for table in tables:
                schema_name = table['table_schema']
                if schema_name not in schemas:
                    schemas[schema_name] = []
                schemas[schema_name].append(table)
            
            # 创建模式节点
            for schema_name, schema_tables in schemas.items():
                schema_item = QTreeWidgetItem(db_item)
                schema_item.setText(0, f"{get_icon('folder')} {schema_name}")
                schema_item.setText(1, "模式")
                schema_item.setText(2, schema_name)
                
                # 创建表节点
                for table in schema_tables:
                    table_name = table['table_name']
                    is_spatial = table['is_spatial']
                    geom_type = table.get('geometry_type', '')
                    table_size = table.get('table_size', '未知')
                    
                    table_item = QTreeWidgetItem(schema_item)
                    icon = get_icon('spatial') if is_spatial else get_icon('table')
                    table_item.setText(0, f"{icon} {table_name}")
                    table_item.setText(1, "空间表" if is_spatial else "普通表")
                    table_item.setText(2, schema_name)
                    table_item.setText(3, geom_type)
                    table_item.setText(4, table_size)
                    
                    # 存储完整信息供重命名使用
                    table_item.setData(0, Qt.ItemDataRole.UserRole, table)
            
            self.pg_tree.expandAll()
            
        except Exception as e:
            log_manager.log_exception("刷新PostgreSQL信息", e)
            QMessageBox.critical(self, "错误", f"刷新PostgreSQL信息失败: {str(e)}")
    
    def on_table_selected(self):
        """表选择变化时的处理"""
        selected_items = self.pg_tree.selectedItems()
        
        # 只有选中的是表时才启用重命名按钮
        if selected_items:
            item = selected_items[0]
            item_type = item.text(1)
            self.pg_rename_btn.setEnabled(item_type in ["空间表", "普通表"])
        else:
            self.pg_rename_btn.setEnabled(False)
    
    def rename_table(self):
        """重命名表"""
        try:
            selected_items = self.pg_tree.selectedItems()
            if not selected_items:
                QMessageBox.warning(self, "警告", "请选择要重命名的表")
                return
                
            item = selected_items[0]
            table_data = item.data(0, Qt.ItemDataRole.UserRole)
            
            if not table_data:
                QMessageBox.warning(self, "警告", "无法获取表信息")
                return
                
            current_name = table_data['table_name']
            schema_name = table_data['table_schema']
            
            dialog = TableRenameDialog(current_name, self)
            if dialog.exec() == QDialog.DialogCode.Accepted:
                new_name = dialog.get_new_name()
                
                if not new_name or new_name == current_name:
                    return
                    
                # 验证新名称
                #if not re.match(r'^[a-zA-Z][a-zA-Z0-9_]*, new_name):
                if not re.match(r'^[a-zA-Z][a-zA-Z0-9_]*$', new_name):
                    QMessageBox.warning(self, "警告", "表名只能包含字母、数字和下划线，且必须以字母开头")
                    return
                
                # 执行重命名
                pg_manager = ImprovedPostgreSQLManager(self.db_connection.params)
                success, message = pg_manager.connect()
                if success:
                    success, message = pg_manager.rename_table(current_name, new_name, schema_name)
                    
                    if success:
                        QMessageBox.information(self, "成功", f"表已重命名为: {new_name}")
                        self.refresh_postgresql_info()
                    else:
                        QMessageBox.critical(self, "错误", f"重命名失败: {message}")
                else:
                    QMessageBox.critical(self, "错误", "数据库连接失败")
                    
        except Exception as e:
            log_manager.log_exception("重命名表", e)
            QMessageBox.critical(self, "错误", f"重命名时发生异常: {str(e)}")
    
    def browse_source(self):
        """浏览数据源"""
        try:
            if self.folder_radio.isChecked():
                folder = QFileDialog.getExistingDirectory(self, "选择数据文件夹")
                if folder:
                    self.source_path_edit.setText(folder)
                    log_manager.log_operation("选择数据源文件夹", folder, True)
            else:
                if self.db_connection.connection:
                    self.source_path_edit.setText("当前PostgreSQL连接")
                else:
                    QMessageBox.warning(self, "警告", "请先连接PostgreSQL数据库")
        except Exception as e:
            log_manager.log_exception("浏览数据源", e)
    
    def scan_data(self):
        """扫描数据"""
        try:
            self.scanned_data = []
            self.data_table.setRowCount(0)
            
            if self.folder_radio.isChecked():
                self.scan_folder_data()
            else:
                self.scan_postgresql_data()
        except Exception as e:
            log_manager.log_exception("扫描数据", e)
            QMessageBox.critical(self, "错误", f"扫描数据失败: {e}")
    
    def scan_folder_data(self):
        """扫描文件夹数据"""
        try:
            folder_path = self.source_path_edit.text().strip()
            if not folder_path or not os.path.exists(folder_path):
                QMessageBox.warning(self, "警告", "请选择有效的文件夹路径")
                return
            
            if not HAS_SPATIAL_LIBS:
                QMessageBox.critical(self, "错误", "缺少空间数据处理库，无法扫描数据")
                return
                
            scanner = ImprovedDataScanner()
            self.scanned_data = scanner.scan_folder(folder_path)
            self.update_data_table()
            
            log_manager.log_operation("扫描文件夹", f"{folder_path}, 找到 {len(self.scanned_data)} 个文件", True)
            QMessageBox.information(self, "完成", 
                f"扫描完成，共找到 {len(self.scanned_data)} 个空间数据文件")
                
        except Exception as e:
            log_manager.log_exception("扫描文件夹数据", e)
            QMessageBox.critical(self, "错误", f"扫描文件夹失败: {str(e)}")
    
    def scan_postgresql_data(self):
        """扫描PostgreSQL数据"""
        try:
            if not self.db_connection.connection:
                QMessageBox.warning(self, "警告", "请先连接PostgreSQL数据库")
                return
                
            spatial_tables = self.db_connection.get_spatial_tables()
            
            self.scanned_data = []
            for table in spatial_tables:
                schema_name = table['table_schema']
                table_name = table['table_name']
                geom_type = table.get('geometry_type', '')
                srid = table.get('srid', 4326)
                size = table.get('table_size', '未知')
                
                full_name = f"{schema_name}.{table_name}"
                
                self.scanned_data.append({
                    'original_name': full_name,
                    'path': full_name,
                    'type': "空间表",
                    'size': size,
                    'srs': f"EPSG:{srid}" if srid else "未知",
                    'new_name': table_name,
                    'style': 'default',
                    'geometry_type': geom_type,
                    'feature_count': table.get('column_count', '未知'),
                    'extent': None
                })
            
            self.update_data_table()
            
            log_manager.log_operation("扫描PostgreSQL数据", f"找到 {len(self.scanned_data)} 个空间表", True)
            QMessageBox.information(self, "完成",
                f"扫描完成，共找到 {len(self.scanned_data)} 个空间数据表")
                
        except Exception as e:
            log_manager.log_exception("扫描PostgreSQL数据", e)
            QMessageBox.critical(self, "错误", f"扫描PostgreSQL数据失败: {str(e)}")
    
    def update_data_table(self):
        """更新数据表格"""
        try:
            self.data_table.setRowCount(len(self.scanned_data))
            
            for row, data in enumerate(self.scanned_data):
                self.data_table.setItem(row, 0, QTableWidgetItem(data['original_name']))
                self.data_table.setItem(row, 1, QTableWidgetItem(data['type']))
                self.data_table.setItem(row, 2, QTableWidgetItem(data['size']))
                self.data_table.setItem(row, 3, QTableWidgetItem(data['srs']))
                self.data_table.setItem(row, 4, QTableWidgetItem(data['new_name']))
                self.data_table.setItem(row, 5, QTableWidgetItem(data['style']))
                self.data_table.setItem(row, 6, QTableWidgetItem(str(data.get('feature_count', ''))))
        except Exception as e:
            log_manager.log_exception("更新数据表格", e)
    
    def on_cell_changed(self, row, column):
        """单元格内容改变时同步到数据"""
        try:
            if 0 <= row < len(self.scanned_data):
                item = self.data_table.item(row, column)
                if item:
                    value = item.text()
                    
                    if column == 3:  # 坐标系
                        self.scanned_data[row]['srs'] = value
                    elif column == 4:  # 新名称
                        # 规范化名称
                        normalized = ImprovedDataScanner.normalize_name(value)
                        self.scanned_data[row]['new_name'] = normalized
                        # 更新表格显示
                        if normalized != value:
                            item.setText(normalized)
                    elif column == 5:  # 样式
                        self.scanned_data[row]['style'] = value
        except Exception as e:
            log_manager.log_exception("单元格内容变化", e)
    
    def batch_rename(self):
        """批量重命名"""
        try:
            if not self.scanned_data:
                QMessageBox.warning(self, "警告", "没有扫描到数据")
                return
                
            # 简单的批量重命名对话框
            dialog = QDialog(self)
            dialog.setWindowTitle("批量重命名")
            dialog.setModal(True)
            dialog.resize(400, 200)
            
            layout = QVBoxLayout()
            
            # 添加前缀
            prefix_layout = QHBoxLayout()
            prefix_edit = QLineEdit()
            prefix_layout.addWidget(QLabel("添加前缀:"))
            prefix_layout.addWidget(prefix_edit)
            layout.addLayout(prefix_layout)
            
            # 按钮
            buttons = QDialogButtonBox(QDialogButtonBox.StandardButton.Ok | QDialogButtonBox.StandardButton.Cancel)
            buttons.accepted.connect(dialog.accept)
            buttons.rejected.connect(dialog.reject)
            layout.addWidget(buttons)
            
            dialog.setLayout(layout)
            
            if dialog.exec() == QDialog.DialogCode.Accepted:
                prefix = prefix_edit.text().strip()
                if prefix:
                    for i, data in enumerate(self.scanned_data):
                        new_name = f"{prefix}_{data['new_name']}"
                        self.scanned_data[i]['new_name'] = ImprovedDataScanner.normalize_name(new_name)
                    
                    self.update_data_table()
                    log_manager.log_operation("批量重命名", f"前缀: {prefix}", True)
                    QMessageBox.information(self, "成功", "批量重命名完成")
        except Exception as e:
            log_manager.log_exception("批量重命名", e)
            QMessageBox.critical(self, "错误", f"批量重命名失败: {e}")
    
    def batch_set_style(self):
        """批量设置样式"""
        try:
            if not self.scanned_data:
                QMessageBox.warning(self, "警告", "没有扫描到数据")
                return
                
            dialog = StyleDialog(self.available_styles, self)
            if dialog.exec() == QDialog.DialogCode.Accepted:
                selected_style = dialog.get_selected_style()
                
                for i, data in enumerate(self.scanned_data):
                    self.scanned_data[i]['style'] = selected_style
                
                self.update_data_table()
                log_manager.log_operation("批量设置样式", selected_style, True)
                QMessageBox.information(self, "成功", "批量样式设置完成")
        except Exception as e:
            log_manager.log_exception("批量设置样式", e)
            QMessageBox.critical(self, "错误", f"批量设置样式失败: {e}")
    
    def refresh_workspaces(self):
        """刷新工作空间"""
        if not self.gs_connection.connected:
            return
            
        try:
            workspaces = self.gs_connection.get_workspaces()
            workspace_names = [ws.get('name', '') for ws in workspaces]
            
            self.workspace_combo.clear()
            self.workspace_combo.addItems(workspace_names)
            
            self.style_workspace_combo.clear()
            self.style_workspace_combo.addItems([''] + workspace_names)
            
            self.workspace_filter_combo.clear()
            self.workspace_filter_combo.addItems([''] + workspace_names)
            
        except Exception as e:
            log_manager.log_exception("刷新工作空间", e)
    
    def import_to_postgresql(self):
        """导入数据到PostgreSQL"""
        try:
            if not self.scanned_data:
                QMessageBox.warning(self, "警告", "请先扫描数据")
                return
                
            if not self.db_connection.connection:
                QMessageBox.warning(self, "警告", "请先连接PostgreSQL数据库")
                return
            
            if not HAS_SPATIAL_LIBS:
                QMessageBox.critical(self, "错误", "缺少空间数据处理库，无法导入数据")
                return
            
            # 确认导入
            reply = QMessageBox.question(self, "确认", 
                f"确定要导入 {len(self.scanned_data)} 个数据项到PostgreSQL吗？")
            
            if reply != QMessageBox.StandardButton.Yes:
                return
            
            # 创建工作线程
            def import_task():
                try:
                    pg_manager = ImprovedPostgreSQLManager(self.db_connection.params)
                    success, message = pg_manager.connect()
                    if not success:
                        return False, f"数据库连接失败: {message}"
                    
                    success_count = 0
                    total_count = len(self.scanned_data)
                    errors = []
                    
                    for i, item in enumerate(self.scanned_data):
                        # 更新进度
                        progress = int((i / total_count) * 100)
                        self.progress_bar.setValue(progress)
                        self.status_label.setText(f"正在导入: {item['new_name']}")
                        
                        try:
                            file_path = item['path']
                            table_name = item['new_name']
                            data_type = item['type']
                            srid_text = item.get('srs', 'EPSG:4326')
                            target_crs = srid_text if srid_text.startswith('EPSG:') else 'EPSG:4326'
                            
                            if data_type == "矢量数据":
                                success, message = pg_manager.import_vector_file(
                                    file_path, table_name, target_crs=target_crs
                                )
                                if success:
                                    success_count += 1
                                else:
                                    errors.append(f"{table_name}: {message}")
                                    
                            elif data_type == "栅格数据":
                                success, message = pg_manager.import_raster_file(
                                    file_path, table_name, target_crs=target_crs
                                )
                                if success:
                                    success_count += 1
                                else:
                                    errors.append(f"{table_name}: {message}")
                                    
                            elif data_type == "空间表":
                                # 已在数据库中，跳过
                                success_count += 1
                                
                        except Exception as e:
                            errors.append(f"{item['new_name']}: {str(e)}")
                            self.logger.error(f"导入 {item['new_name']} 失败: {e}")
                    
                    self.progress_bar.setValue(100)
                    result_message = f"导入完成: 成功 {success_count}/{total_count}"
                    if errors:
                        result_message += f"\n错误: {len(errors)} 个"
                    
                    self.status_label.setText(result_message)
                    
                    return success_count > 0, result_message
                    
                except Exception as e:
                    return False, f"导入过程中发生错误: {str(e)}"
            
            # 启动导入任务
            thread = WorkerThread(import_task)
            thread.finished.connect(self.on_import_finished)
            thread.start()
            
        except Exception as e:
            log_manager.log_exception("导入到PostgreSQL", e)
            QMessageBox.critical(self, "错误", f"导入失败: {e}")
    
    def on_import_finished(self, success, message):
        """导入完成处理"""
        try:
            if success:
                QMessageBox.information(self, "成功", message)
                # 刷新PostgreSQL信息
                self.refresh_postgresql_info()
            else:
                QMessageBox.critical(self, "错误", message)
            
            self.progress_bar.setValue(0)
            self.status_label.setText("就绪")
        except Exception as e:
            log_manager.log_exception("导入完成处理", e)
    
    def publish_to_geoserver(self):
        """发布数据到GeoServer"""
        try:
            if not self.scanned_data:
                QMessageBox.warning(self, "警告", "请先扫描数据")
                return
                
            if not self.gs_connection.connected:
                QMessageBox.warning(self, "警告", "请先连接GeoServer")
                return
                
            if not self.db_connection.connection:
                QMessageBox.warning(self, "警告", "请先连接PostgreSQL数据库")
                return
            
            workspace = self.workspace_combo.currentText().strip()
            if not workspace:
                QMessageBox.warning(self, "警告", "请选择或输入工作空间名称")
                return
            
            # 确认发布
            reply = QMessageBox.question(self, "确认", 
                f"确定要发布 {len(self.scanned_data)} 个图层到工作空间 '{workspace}' 吗？")
            
            if reply != QMessageBox.StandardButton.Yes:
                return
            
            # 创建工作线程
            def publish_task():
                try:
                    # 创建批处理器
                    gs_config = {
                        'base_url': self.gs_connection.base_url,
                        'username': self.gs_connection.username,
                        'password': self.gs_connection.password
                    }
                    
                    processor = ImprovedBatchProcessor(self.db_connection.params, gs_config)
                    
                    def progress_callback(value):
                        self.progress_bar.setValue(value)
                    
                    def status_callback(status):
                        self.status_label.setText(status)
                    
                    # 执行批量发布
                    success, message = processor.process_data_items(
                        self.scanned_data,
                        workspace,
                        f"{workspace}_datastore",
                        progress_callback,
                        status_callback
                    )
                    
                    return success, message
                    
                except Exception as e:
                    return False, f"发布过程中发生错误: {str(e)}"
            
            # 启动发布任务
            thread = WorkerThread(publish_task)
            thread.finished.connect(self.on_publish_finished)
            thread.start()
            
        except Exception as e:
            log_manager.log_exception("发布到GeoServer", e)
            QMessageBox.critical(self, "错误", f"发布失败: {e}")
    
    def on_publish_finished(self, success, message):
        """发布完成处理"""
        try:
            if success:
                QMessageBox.information(self, "成功", message)
                # 刷新GeoServer和图层信息
                self.refresh_geoserver_info()
                self.refresh_published_layers()
            else:
                QMessageBox.critical(self, "错误", message)
            
            self.progress_bar.setValue(0)
            self.status_label.setText("就绪")
        except Exception as e:
            log_manager.log_exception("发布完成处理", e)
    
    def import_and_publish(self):
        """一键导入发布"""
        try:
            if not self.scanned_data:
                QMessageBox.warning(self, "警告", "请先扫描数据")
                return
                
            if not self.db_connection.connection:
                QMessageBox.warning(self, "警告", "请先连接PostgreSQL数据库")
                return
                
            if not self.gs_connection.connected:
                QMessageBox.warning(self, "警告", "请先连接GeoServer")
                return
            
            if not HAS_SPATIAL_LIBS:
                QMessageBox.critical(self, "错误", "缺少空间数据处理库，无法执行此操作")
                return
            
            workspace = self.workspace_combo.currentText().strip()
            if not workspace:
                QMessageBox.warning(self, "警告", "请选择或输入工作空间名称")
                return
            
            # 确认操作
            reply = QMessageBox.question(self, "确认", 
                f"确定要导入并发布 {len(self.scanned_data)} 个数据项吗？\n"
                f"工作空间: {workspace}")
            
            if reply != QMessageBox.StandardButton.Yes:
                return
            
            # 创建工作线程
            def import_publish_task():
                try:
                    # 创建批处理器
                    gs_config = {
                        'base_url': self.gs_connection.base_url,
                        'username': self.gs_connection.username,
                        'password': self.gs_connection.password
                    }
                    
                    processor = ImprovedBatchProcessor(self.db_connection.params, gs_config)
                    
                    def progress_callback(value):
                        self.progress_bar.setValue(value)
                    
                    def status_callback(status):
                        self.status_label.setText(status)
                    
                    # 执行一键导入发布
                    success, message = processor.process_data_items(
                        self.scanned_data,
                        workspace,
                        f"{workspace}_datastore",
                        progress_callback,
                        status_callback
                    )
                    
                    return success, message
                    
                except Exception as e:
                    return False, f"操作过程中发生错误: {str(e)}"
            
            # 启动任务
            thread = WorkerThread(import_publish_task)
            thread.finished.connect(self.on_import_publish_finished)
            thread.start()
            
        except Exception as e:
            log_manager.log_exception("一键导入发布", e)
            QMessageBox.critical(self, "错误", f"操作失败: {e}")
    
    def on_import_publish_finished(self, success, message):
        """一键导入发布完成处理"""
        try:
            if success:
                QMessageBox.information(self, "成功", message)
                # 刷新所有相关信息
                self.refresh_postgresql_info()
                self.refresh_geoserver_info()
                self.refresh_published_layers()
            else:
                QMessageBox.critical(self, "错误", message)
            
            self.progress_bar.setValue(0)
            self.status_label.setText("就绪")
        except Exception as e:
            log_manager.log_exception("一键导入发布完成处理", e)
    
    def browse_sld_file(self):
        """浏览SLD文件"""
        try:
            file_path, _ = QFileDialog.getOpenFileName(
                self, "选择SLD文件", "", 
                "SLD文件 (*.sld);;XML文件 (*.xml);;所有文件 (*.*)"
            )
            if file_path:
                self.sld_path_edit.setText(file_path)
                # 自动设置样式名称
                style_name = Path(file_path).stem
                self.style_name_edit.setText(style_name)
                log_manager.log_operation("选择SLD文件", file_path, True)
        except Exception as e:
            log_manager.log_exception("浏览SLD文件", e)
    
    def import_style(self):
        """导入样式"""
        try:
            sld_path = self.sld_path_edit.text().strip()
            style_name = self.style_name_edit.text().strip()
            workspace = self.style_workspace_combo.currentText().strip()
            
            if not sld_path or not os.path.exists(sld_path):
                QMessageBox.warning(self, "警告", "请选择有效的SLD文件")
                return
                
            if not style_name:
                QMessageBox.warning(self, "警告", "请输入样式名称")
                return
                
            if not self.gs_connection.connected:
                QMessageBox.warning(self, "警告", "请先连接GeoServer")
                return
            
            # 读取SLD文件内容
            with open(sld_path, 'r', encoding='utf-8') as f:
                sld_content = f.read()
            
            # 创建GeoServer发布器
            gs_publisher = ImprovedGeoServerPublisher(
                self.gs_connection.base_url,
                self.gs_connection.username,
                self.gs_connection.password
            )
            
            # 上传样式
            success, message = gs_publisher.upload_style(
                style_name, sld_content, workspace if workspace else None
            )
            
            if success:
                log_manager.log_operation("导入样式", f"{style_name} ({workspace or '全局'})", True)
                QMessageBox.information(self, "成功", f"样式导入成功: {style_name}")
                self.refresh_styles()
                # 清空输入框
                self.sld_path_edit.clear()
                self.style_name_edit.clear()
            else:
                QMessageBox.critical(self, "错误", f"样式导入失败: {message}")
                
        except Exception as e:
            log_manager.log_exception("导入样式", e)
            QMessageBox.critical(self, "错误", f"导入样式时发生异常: {str(e)}")
    
    def refresh_styles(self):
        """刷新样式"""
        if not self.gs_connection.connected:
            return
            
        try:
            self.style_tree.clear()
            self.available_styles = []
            
            # 获取全局样式
            global_styles = self.gs_connection.get_styles()
            for style in global_styles:
                style_name = style.get('name', 'unknown')
                style_info = {
                    'name': style_name,
                    'workspace': '全局',
                    'filename': style.get('filename', '')
                }
                self.available_styles.append(style_info)
                
                item = QTreeWidgetItem(self.style_tree)
                item.setText(0, style_name)
                item.setText(1, '全局')
                item.setText(2, style.get('filename', ''))
            
            # 获取工作空间样式
            workspaces = self.gs_connection.get_workspaces()
            for workspace in workspaces:
                ws_name = workspace.get('name', '')
                ws_styles = self.gs_connection.get_styles(ws_name)
                
                for style in ws_styles:
                    style_name = style.get('name', 'unknown')
                    style_info = {
                        'name': f"{ws_name}:{style_name}",
                        'workspace': ws_name,
                        'filename': style.get('filename', '')
                    }
                    self.available_styles.append(style_info)
                    
                    item = QTreeWidgetItem(self.style_tree)
                    item.setText(0, style_name)
                    item.setText(1, ws_name)
                    item.setText(2, style.get('filename', ''))
                    
        except Exception as e:
            log_manager.log_exception("刷新样式", e)
    
    def filter_layers(self):
        """筛选图层"""
        self.refresh_published_layers()
    
    def refresh_published_layers(self):
        """刷新已发布图层"""
        if not self.gs_connection.connected:
            return
            
        try:
            self.layers_table.setRowCount(0)
            
            workspaces = self.gs_connection.get_workspaces()
            workspace_filter = self.workspace_filter_combo.currentText()
            layer_filter = self.layer_name_filter_edit.text().strip().lower()
            
            row = 0
            for workspace in workspaces:
                ws_name = workspace.get('name', '')
                
                # 应用工作空间筛选
                if workspace_filter and workspace_filter != ws_name:
                    continue
                
                layers = self.gs_connection.get_layers(ws_name)
                for layer in layers:
                    layer_name = layer.get('name', '')
                    
                    # 应用图层名称筛选
                    if layer_filter and layer_filter not in layer_name.lower():
                        continue
                    
                    self.layers_table.insertRow(row)
                    self.layers_table.setItem(row, 0, QTableWidgetItem(layer_name))
                    self.layers_table.setItem(row, 1, QTableWidgetItem(ws_name))
                    self.layers_table.setItem(row, 2, QTableWidgetItem("默认样式"))
                    self.layers_table.setItem(row, 3, QTableWidgetItem("PostGIS"))
                    self.layers_table.setItem(row, 4, QTableWidgetItem(
                        datetime.now().strftime("%Y-%m-%d")
                    ))
                    row += 1
                    
        except Exception as e:
            log_manager.log_exception("刷新已发布图层", e)
            QMessageBox.critical(self, "错误", f"刷新图层失败: {str(e)}")

def create_default_styles():
    """创建默认样式"""
    
    styles = {
        'default_point': '''<?xml version="1.0" encoding="UTF-8"?>
<StyledLayerDescriptor version="1.0.0" xmlns="http://www.opengis.net/sld">
  <NamedLayer>
    <Name>default_point</Name>
    <UserStyle>
      <Title>Default Point Style</Title>
      <FeatureTypeStyle>
        <Rule>
          <PointSymbolizer>
            <Graphic>
              <Mark>
                <WellKnownName>circle</WellKnownName>
                <Fill>
                  <CssParameter name="fill">#FF4444</CssParameter>
                  <CssParameter name="fill-opacity">0.8</CssParameter>
                </Fill>
                <Stroke>
                  <CssParameter name="stroke">#000000</CssParameter>
                  <CssParameter name="stroke-width">1</CssParameter>
                </Stroke>
              </Mark>
              <Size>8</Size>
            </Graphic>
          </PointSymbolizer>
        </Rule>
      </FeatureTypeStyle>
    </UserStyle>
  </NamedLayer>
</StyledLayerDescriptor>''',

        'default_line': '''<?xml version="1.0" encoding="UTF-8"?>
<StyledLayerDescriptor version="1.0.0" xmlns="http://www.opengis.net/sld">
  <NamedLayer>
    <Name>default_line</Name>
    <UserStyle>
      <Title>Default Line Style</Title>
      <FeatureTypeStyle>
        <Rule>
          <LineSymbolizer>
            <Stroke>
              <CssParameter name="stroke">#4444FF</CssParameter>
              <CssParameter name="stroke-width">2</CssParameter>
              <CssParameter name="stroke-opacity">0.9</CssParameter>
            </Stroke>
          </LineSymbolizer>
        </Rule>
      </FeatureTypeStyle>
    </UserStyle>
  </NamedLayer>
</StyledLayerDescriptor>''',

        'default_polygon': '''<?xml version="1.0" encoding="UTF-8"?>
<StyledLayerDescriptor version="1.0.0" xmlns="http://www.opengis.net/sld">
  <NamedLayer>
    <Name>default_polygon</Name>
    <UserStyle>
      <Title>Default Polygon Style</Title>
      <FeatureTypeStyle>
        <Rule>
          <PolygonSymbolizer>
            <Fill>
              <CssParameter name="fill">#44FF44</CssParameter>
              <CssParameter name="fill-opacity">0.6</CssParameter>
            </Fill>
            <Stroke>
              <CssParameter name="stroke">#000000</CssParameter>
              <CssParameter name="stroke-width">1</CssParameter>
              <CssParameter name="stroke-opacity">0.9</CssParameter>
            </Stroke>
          </PolygonSymbolizer>
        </Rule>
      </FeatureTypeStyle>
    </UserStyle>
  </NamedLayer>
</StyledLayerDescriptor>'''
    }
    
    return styles

def main():
    """主函数"""
    try:
        app = QApplication(sys.argv)
        
        # 设置应用样式
        app.setStyle('Fusion')
        
        # 设置应用程序图标和信息
        app.setApplicationName("GeoServer & PostgreSQL 数据管理系统")
        app.setApplicationVersion("2.1")
        app.setOrganizationName("GIS Development Team")
        
        # 记录应用启动
        logger.info("应用程序启动")
        
        # 创建主窗口
        window = ImprovedMainWindow()
        window.show()
        
        # 显示启动信息
        startup_message = (
            "欢迎使用 GeoServer & PostgreSQL 数据管理系统 V2.1\n\n"
            "主要改进:\n"
            "• 移除了GDAL外部工具依赖，使用纯Python库\n"
            "• 添加了完整的日志追踪功能\n"
            "• 改进了错误处理和异常管理\n"
            "• 增强了数据处理稳定性\n\n"
            "主要功能:\n"
            "• GeoServer 连接和资源管理\n"
            "• PostgreSQL 空间数据库管理\n"
            "• 批量数据导入和发布\n"
            "• 样式管理和图层监控\n"
            "• 完整的操作日志记录\n\n"
            "使用前请确保已安装空间数据处理库:\n"
            "pip install geopandas fiona rasterio"
        )
        
        QMessageBox.information(window, "欢迎", startup_message)
        
        logger.info("应用程序界面显示完成")
        
        # 运行应用
        result = app.exec()
        
        logger.info("应用程序退出")
        return result
        
    except Exception as e:
        logger.error(f"应用程序启动失败: {e}")
        logger.error(f"详细错误: {traceback.format_exc()}")
        
        if 'app' in locals():
            QMessageBox.critical(None, "严重错误", 
                f"应用程序启动失败:\n{str(e)}\n\n"
                "请检查日志文件获取详细信息。")
        
        return 1

if __name__ == '__main__':
    sys.exit(main())