"""
Hyperysco-Map - Export DXF Topographique Professionnel
Application complète avec authentification
"""

from flask import Flask, render_template, request, jsonify, send_file, redirect, url_for, session, flash
import numpy as np
import json
import os
import tempfile
import zipfile
import traceback
import ezdxf
from ezdxf import units
from ezdxf import colors as dxf_colors
import time
import requests
from io import BytesIO
from pyproj import Transformer
import sqlite3
import hashlib
from functools import wraps
from datetime import datetime
import math

app = Flask(__name__)
app.secret_key = os.environ.get('SECRET_KEY', 'hyperysco-map-secret-key-2026-ELHCH-ACHACH')

# ============================================================
# BASE DE DONNÉES
# ============================================================

DB_PATH = os.path.join(os.path.dirname(__file__), 'hyperysco.db')

def get_db():
    """Connexion à la base de données"""
    conn = sqlite3.connect(DB_PATH)
    conn.row_factory = sqlite3.Row
    return conn

def hash_password(password):
    """Hash un mot de passe"""
    return hashlib.sha256(password.encode()).hexdigest()

def init_db():
    """Initialise la DB si nécessaire"""
    if not os.path.exists(DB_PATH):
        conn = get_db()
        cursor = conn.cursor()
        
        cursor.execute('''
            CREATE TABLE IF NOT EXISTS users (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                username TEXT UNIQUE NOT NULL,
                password TEXT NOT NULL,
                email TEXT,
                plan TEXT DEFAULT 'free',
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                exports_count INTEGER DEFAULT 0
            )
        ''')

        cursor.execute('''
            CREATE TABLE IF NOT EXISTS exports (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id INTEGER NOT NULL,
                filename TEXT,
                location TEXT,
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                FOREIGN KEY (user_id) REFERENCES users(id)
            )
        ''')
        
        # Utilisateurs par défaut
        users = [
            ('ELHCH', hash_password('ELHCH'), 'elhch@hyperysco.ma', 'premium'),
            ('ACHACH', hash_password('ACHACH'), 'achach@hyperysco.ma', 'premium'),
        ]
        
        for u in users:
            try:
                cursor.execute('INSERT INTO users (username, password, email, plan) VALUES (?,?,?,?)', u)
            except:
                pass
        
        conn.commit()
        conn.close()

# Initialiser la DB au démarrage
init_db()

# ============================================================
# AUTHENTIFICATION
# ============================================================

def login_required(f):
    """Décorateur pour protéger les routes"""
    @wraps(f)
    def decorated_function(*args, **kwargs):
        if 'user_id' not in session:
            return redirect(url_for('login'))
        return f(*args, **kwargs)
    return decorated_function

def get_current_user():
    """Récupère l'utilisateur connecté"""
    if 'user_id' not in session:
        return None
    conn = get_db()
    user = conn.execute('SELECT * FROM users WHERE id = ?', (session['user_id'],)).fetchone()
    conn.close()
    return user

# ============================================================
# CONFIGURATION
# ============================================================

OVERPASS_SERVERS = [
    "https://overpass-api.de/api/interpreter",
    "https://overpass.kumi.systems/api/interpreter",
    "https://maps.mail.ru/osm/tools/overpass/api/interpreter",
]

# Les serveurs Overpass rejettent (406/429) les requêtes sans User-Agent identifiable
OVERPASS_HEADERS = {
    "User-Agent": "HyperyscoMap/1.0 (contact: elhch@hyperysco.ma)",
    "Accept": "application/json",
}

# Couleurs AutoCAD ACI
COLORS = {
    'CONTOUR_MAJOR': 8,     # Gris foncé
    'CONTOUR_MINOR': 9,     # Gris clair
    'ROAD_PRIMARY': 1,      # Rouge
    'ROAD_SECONDARY': 2,    # Jaune
    'ROAD_OTHER': 7,        # Blanc
    'BUILDING': 30,         # Orange
    'WATER': 5,             # Bleu
    'LANDUSE': 3,           # Vert
    'ROAD_LABELS': 6,       # Magenta (noms des rues)
    'LAMBERT_CROSS': 200,   # Violet foncé (croix Lambert - identifiable)
    'LAMBERT_TEXT': 200,    # Violet foncé (texte coordonnées)
    'PLACES': 6,            # Magenta (noms quartiers)
    'SEARCH_MARKER': 40,    # Orange vif (étoile de repérage)
}

# Projection Lambert Zone I Maroc (comme sur tool-online.com)
# EPSG:26191 - Merchich / Nord Maroc
LAMBERT_MAROC_ZONE1 = "+proj=lcc +lat_1=33.3 +lat_0=33.3 +lon_0=-5.4 +k_0=0.999625769 +x_0=500000 +y_0=300000 +a=6378249.2 +b=6356515 +towgs84=31,146,47,0,0,0,0 +units=m +no_defs"

# ============================================================
# PROJECTION - Convertit lat/lon en mètres locaux
# ============================================================

def get_local_projection(bbox):
    """
    Crée une projection locale centrée sur la bbox.
    Retourne un transformer qui convertit WGS84 -> mètres locaux.
    """
    south, west, north, east = bbox
    center_lat = (south + north) / 2
    center_lon = (west + east) / 2
    
    # Projection Transverse Mercator centrée sur la zone
    proj_string = f"+proj=tmerc +lat_0={center_lat} +lon_0={center_lon} +k=1 +x_0=0 +y_0=0 +datum=WGS84 +units=m"
    
    transformer = Transformer.from_crs("EPSG:4326", proj_string, always_xy=True)
    return transformer


def get_lambert_transformer():
    """
    Crée un transformer WGS84 -> Lambert Zone I Maroc.
    Pour les croix de calage Covadis.
    """
    transformer = Transformer.from_crs(
        "EPSG:4326",
        LAMBERT_MAROC_ZONE1,
        always_xy=True
    )
    return transformer


def generate_lambert_crosses(bbox, transformer_local, transformer_lambert, spacing=200):
    """
    Génère une grille UNIFORME de croix avec coordonnées Lambert.
    Le nombre de graduations est le MÊME en X et Y pour une grille carrée.
    
    Args:
        bbox: [south, west, north, east] en WGS84
        transformer_local: transformer vers coordonnées locales
        transformer_lambert: transformer vers Lambert Maroc
        spacing: espacement en mètres entre les croix
    
    Returns:
        Liste de dict avec position locale et coordonnées Lambert
    """
    south, west, north, east = bbox
    
    # Calculer la taille de la zone en mètres
    x_min, y_min = transformer_local.transform(west, south)
    x_max, y_max = transformer_local.transform(east, north)
    
    width = x_max - x_min
    height = y_max - y_min
    
    # GRILLE UNIFORME: même nombre de graduations X et Y
    # Basé sur la plus grande dimension
    max_dim = max(width, height)
    n_divisions = max(2, min(5, int(max_dim / spacing) + 1))  # Entre 2 et 5 divisions
    
    # Appliquer le même nombre pour X et Y
    n_cols = n_divisions
    n_rows = n_divisions
    
    print(f"    Grille uniforme: {n_cols} x {n_rows} croix")
    
    crosses = []
    
    # Grille de points en WGS84
    lats = np.linspace(south, north, n_rows)
    lons = np.linspace(west, east, n_cols)
    
    for lat in lats:
        for lon in lons:
            # Coordonnées locales (pour placement dans DXF)
            x_local, y_local = transformer_local.transform(lon, lat)
            
            # Coordonnées Lambert Maroc Zone I (pour affichage)
            x_lambert, y_lambert = transformer_lambert.transform(lon, lat)
            
            crosses.append({
                'x_local': round(x_local, 2),
                'y_local': round(y_local, 2),
                'x_lambert': round(x_lambert, 3),
                'y_lambert': round(y_lambert, 3),
                'lon': lon,
                'lat': lat
            })
    
    return crosses

# ============================================================
# RÉCUPÉRATION DONNÉES OSM
# ============================================================

def fetch_osm_data(bbox, layer_type):
    """
    Récupère les données OSM pour une couche spécifique.
    Retourne une liste de dictionnaires avec geometry et properties.
    """
    south, west, north, east = bbox
    bbox_str = f"{south},{west},{north},{east}"
    
    # Requêtes Overpass selon le type
    queries = {
        'roads': f"""
            [out:json][timeout:60];
            (
              way["highway"]["highway"!~"path|footway|cycleway|steps"]({bbox_str});
            );
            out body geom;
        """,
        'buildings': f"""
            [out:json][timeout:60];
            (
              way["building"]({bbox_str});
              relation["building"]({bbox_str});
            );
            out body geom;
        """,
        'water': f"""
            [out:json][timeout:60];
            (
              way["natural"="water"]({bbox_str});
              way["waterway"]({bbox_str});
              relation["natural"="water"]({bbox_str});
            );
            out body geom;
        """,
        'landuse': f"""
            [out:json][timeout:60];
            (
              way["landuse"]({bbox_str});
              relation["landuse"]({bbox_str});
            );
            out body geom;
        """,
        'places': f"""
            [out:json][timeout:60];
            (
              node["place"~"suburb|neighbourhood|quarter|locality|hamlet|village|town"]({bbox_str});
              node["name"]["place"]({bbox_str});
              way["place"]({bbox_str});
            );
            out body geom center;
        """
    }
    
    query = queries.get(layer_type)
    if not query:
        return []
    
    # Essayer les serveurs
    for server in OVERPASS_SERVERS:
        try:
            for attempt in range(3):
                response = requests.post(
                    server,
                    data={'data': query},
                    headers=OVERPASS_HEADERS,
                    timeout=90
                )
                if response.status_code != 429:
                    break
                time.sleep(3 * (attempt + 1))
            if response.status_code == 200:
                data = response.json()
                return parse_osm_elements(data.get('elements', []), layer_type)
            print(f"    Overpass {server} -> HTTP {response.status_code} ({layer_type})")
        except Exception as e:
            print(f"    Overpass {server} -> erreur {e} ({layer_type})")
            continue
    
    return []

def parse_osm_elements(elements, layer_type):
    """Parse les éléments OSM en géométries"""
    results = []
    
    for el in elements:
        el_type = el.get('type')
        
        # Traitement spécial pour les places (nodes)
        if layer_type == 'places':
            tags = el.get('tags', {})
            name = tags.get('name', '') or tags.get('name:fr', '') or tags.get('name:ar', '')
            if not name:
                continue
            
            # Pour les nodes, utiliser lat/lon directement
            if el_type == 'node':
                lat = el.get('lat')
                lon = el.get('lon')
                if lat and lon:
                    results.append({
                        'coords': [(lon, lat)],
                        'type': 'places',
                        'subtype': tags.get('place', 'locality'),
                        'name': name,
                        'closed': False,
                        'is_point': True
                    })
            # Pour les ways, utiliser le centre
            elif el_type == 'way' and el.get('center'):
                center = el.get('center')
                results.append({
                    'coords': [(center['lon'], center['lat'])],
                    'type': 'places',
                    'subtype': tags.get('place', 'locality'),
                    'name': name,
                    'closed': False,
                    'is_point': True
                })
            continue
        
        # Traitement normal pour les ways
        if el_type != 'way':
            continue
        
        geom = el.get('geometry', [])
        if not geom or len(geom) < 2:
            continue
        
        coords = [(p['lon'], p['lat']) for p in geom]
        
        # Classifier les routes et récupérer le nom
        road_class = 'other'
        road_name = ''
        if layer_type == 'roads':
            tags = el.get('tags', {})
            highway = tags.get('highway', 'other')
            if highway in ['motorway', 'trunk', 'primary']:
                road_class = 'primary'
            elif highway in ['secondary', 'tertiary']:
                road_class = 'secondary'
            else:
                road_class = 'other'
            
            # Récupérer le nom de la rue
            road_name = tags.get('name', '') or tags.get('name:fr', '') or tags.get('name:ar', '')
        
        results.append({
            'coords': coords,
            'type': layer_type,
            'subtype': road_class,
            'name': road_name,
            'closed': coords[0] == coords[-1] if len(coords) >= 3 else False
        })
    
    return results

# ============================================================
# GÉNÉRATION COURBES DE NIVEAU
# ============================================================

def get_elevation_data(bbox, resolution=40):
    """
    Récupère les données d'élévation depuis Open-Elevation API.
    Retourne une grille d'élévation.
    """
    south, west, north, east = bbox
    
    # Créer grille de points
    lats = np.linspace(south, north, resolution)
    lons = np.linspace(west, east, resolution)
    
    points = []
    for lat in lats:
        for lon in lons:
            points.append({'latitude': lat, 'longitude': lon})
    
    # Requête API
    try:
        response = requests.post(
            'https://api.open-elevation.com/api/v1/lookup',
            json={'locations': points},
            timeout=60
        )
        
        if response.status_code == 200:
            results = response.json().get('results', [])
            elevations = np.array([r['elevation'] for r in results])
            grid = elevations.reshape((resolution, resolution))
            return grid, lats, lons, 'real'
    except:
        pass
    
    # Fallback: terrain simulé
    print("  ⚠ Utilisation terrain simulé")
    return generate_simulated_terrain(resolution), lats, lons, 'simulated'

def generate_simulated_terrain(resolution):
    """Génère un terrain simulé réaliste"""
    x = np.linspace(0, 4*np.pi, resolution)
    y = np.linspace(0, 4*np.pi, resolution)
    X, Y = np.meshgrid(x, y)
    
    # Combinaison de sinusoïdes pour un relief réaliste
    terrain = (
        50 + 
        20 * np.sin(X/2) * np.cos(Y/2) +
        10 * np.sin(X) * np.sin(Y) +
        5 * np.random.randn(resolution, resolution)
    )
    
    return terrain

def generate_contours(bbox, elevation_grid, lats, lons, interval=10, transformer=None):
    """
    Génère les courbes de niveau à partir de la grille d'élévation.
    Retourne les lignes en coordonnées locales (mètres).
    """
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    
    # Définir les niveaux de contour
    z_min = elevation_grid.min()
    z_max = elevation_grid.max()
    
    levels = np.arange(
        np.floor(z_min / interval) * interval,
        np.ceil(z_max / interval) * interval + interval,
        interval
    )
    
    # Créer les contours avec matplotlib
    fig, ax = plt.subplots()
    
    X, Y = np.meshgrid(lons, lats)
    cs = ax.contour(X, Y, elevation_grid, levels=levels)
    
    plt.close(fig)
    
    # Extraire les lignes
    contour_lines = []
    
    for level_idx, level in enumerate(cs.levels):
        is_major = int(level) % 50 == 0
        
        try:
            # Nouvelle API matplotlib (3.8+)
            if hasattr(cs, 'allsegs') and level_idx < len(cs.allsegs):
                for segment in cs.allsegs[level_idx]:
                    if len(segment) >= 2:
                        # Convertir en coordonnées locales
                        local_coords = []
                        for point in segment:
                            lon, lat = point[0], point[1]
                            x, y = transformer.transform(lon, lat)
                            local_coords.append((round(x, 2), round(y, 2)))
                        
                        if len(local_coords) >= 2:
                            contour_lines.append({
                                'coords': local_coords,
                                'elevation': float(level),
                                'is_major': is_major
                            })
        except Exception as e:
            print(f"  Erreur contour niveau {level}: {e}")
            continue
    
    return contour_lines

# ============================================================
# CRÉATION DXF
# ============================================================

def create_dxf(data, filepath, mode='2d'):
    """
    Crée un fichier DXF avec les données fournies.
    Coordonnées en mètres, origines près de (0,0).
    Utilise des LINE individuelles pour compatibilité maximale.
    """
    # R2004 pour bonne compatibilité et LWPOLYLINE support
    doc = ezdxf.new('R2004')
    
    msp = doc.modelspace()
    
    # Créer les calques
    layers_info = {
        'CONTOUR_MAJOR': COLORS['CONTOUR_MAJOR'],
        'CONTOUR_MINOR': COLORS['CONTOUR_MINOR'],
        'ROADS_PRIMARY': COLORS['ROAD_PRIMARY'],
        'ROADS_SECONDARY': COLORS['ROAD_SECONDARY'],
        'ROADS_OTHER': COLORS['ROAD_OTHER'],
        'BUILDINGS': COLORS['BUILDING'],
        'WATER': COLORS['WATER'],
        'LANDUSE': COLORS['LANDUSE'],
        'ROAD_LABELS': COLORS['ROAD_LABELS'],
        'LAMBERT_CROSS': COLORS['LAMBERT_CROSS'],
        'LAMBERT_TEXT': COLORS['LAMBERT_TEXT'],
        'PLACES': COLORS['PLACES'],
    }
    
    for name, color in layers_info.items():
        layer = doc.layers.add(name)
        layer.color = color
    
    # Style de texte pour les labels
    try:
        doc.styles.add('LABELS', font='Arial')
        doc.styles.add('PLACES', font='Arial')
    except:
        pass
    
    entity_count = 0
    x_coords = []
    y_coords = []
    
    # ===== COURBES DE NIVEAU =====
    for contour in data.get('contours', []):
        coords = contour['coords']
        elevation = contour['elevation']
        is_major = contour['is_major']
        
        if len(coords) < 2:
            continue
        
        layer = 'CONTOUR_MAJOR' if is_major else 'CONTOUR_MINOR'
        
        # Ajouter les coordonnées pour le tracking
        for c in coords:
            x_coords.append(c[0])
            y_coords.append(c[1])
        
        if mode == '3d':
            # Polyline 3D avec élévation Z
            points_3d = [(c[0], c[1], elevation) for c in coords]
            msp.add_3dpolyline(points_3d, dxfattribs={'layer': layer})
        else:
            # Polyline 2D
            msp.add_lwpolyline(coords, dxfattribs={'layer': layer})
        
        entity_count += 1
    
    # ===== ROUTES =====
    road_names_added = set()  # Éviter les doublons
    
    for item in data.get('roads', []):
        coords = item['coords']
        subtype = item.get('subtype', 'other')
        road_name = item.get('name', '')
        
        if len(coords) < 2:
            continue
        
        layer = f'ROADS_{subtype.upper()}'
        if layer not in layers_info:
            layer = 'ROADS_OTHER'
        
        for c in coords:
            x_coords.append(c[0])
            y_coords.append(c[1])
        
        msp.add_lwpolyline(coords, dxfattribs={'layer': layer})
        entity_count += 1
        
        # Ajouter le nom de la rue (si disponible et pas déjà ajouté)
        if road_name and road_name not in road_names_added and len(coords) >= 3:
            road_names_added.add(road_name)
            
            # Position au milieu de la route
            mid_idx = len(coords) // 2
            mid_x, mid_y = coords[mid_idx]
            
            # Calculer l'angle de la route pour orienter le texte
            if mid_idx + 1 < len(coords):
                dx = coords[mid_idx + 1][0] - coords[mid_idx][0]
                dy = coords[mid_idx + 1][1] - coords[mid_idx][1]
            else:
                dx = coords[mid_idx][0] - coords[mid_idx - 1][0]
                dy = coords[mid_idx][1] - coords[mid_idx - 1][1]
            
            import math
            angle = math.degrees(math.atan2(dy, dx))
            
            # Ajuster l'angle pour que le texte soit toujours lisible
            if angle > 90:
                angle -= 180
            elif angle < -90:
                angle += 180
            
            # Taille du texte proportionnelle (environ 3m de haut)
            text_height = 3.0
            
            try:
                msp.add_text(
                    road_name,
                    dxfattribs={
                        'layer': 'ROAD_LABELS',
                        'height': text_height,
                        'rotation': angle,
                        'style': 'LABELS'
                    }
                ).set_placement((mid_x, mid_y))
                entity_count += 1
            except:
                pass
    
    # ===== BÂTIMENTS =====
    for item in data.get('buildings', []):
        coords = item['coords']
        
        if len(coords) < 3:
            continue
        
        for c in coords:
            x_coords.append(c[0])
            y_coords.append(c[1])
        
        msp.add_lwpolyline(coords, close=True, dxfattribs={'layer': 'BUILDINGS'})
        entity_count += 1
    
    # ===== EAU =====
    for item in data.get('water', []):
        coords = item['coords']
        closed = item.get('closed', False)
        
        if len(coords) < 2:
            continue
        
        for c in coords:
            x_coords.append(c[0])
            y_coords.append(c[1])
        
        msp.add_lwpolyline(coords, close=closed, dxfattribs={'layer': 'WATER'})
        entity_count += 1
    
    # ===== OCCUPATION DU SOL =====
    for item in data.get('landuse', []):
        coords = item['coords']
        
        if len(coords) < 3:
            continue
        
        for c in coords:
            x_coords.append(c[0])
            y_coords.append(c[1])
        
        msp.add_lwpolyline(coords, close=True, dxfattribs={'layer': 'LANDUSE'})
        entity_count += 1
    
    # ===== NOMS DES QUARTIERS/LIEUX =====
    for item in data.get('places', []):
        name = item.get('name', '')
        if not name:
            continue
        
        coords = item['coords']
        if len(coords) < 1:
            continue
        
        x, y = coords[0]
        x_coords.append(x)
        y_coords.append(y)
        
        # Taille du texte selon le type de lieu
        subtype = item.get('subtype', 'locality')
        if subtype in ['town', 'village']:
            text_height = 8.0
        elif subtype in ['suburb', 'quarter']:
            text_height = 6.0
        else:
            text_height = 4.0
        
        try:
            msp.add_text(
                name.upper(),
                dxfattribs={
                    'layer': 'PLACES',
                    'height': text_height,
                    'style': 'PLACES'
                }
            ).set_placement((x, y))
            entity_count += 1
        except:
            pass
    
    # ===== CROIX DE CALAGE LAMBERT =====
    for cross in data.get('lambert_crosses', []):
        x = cross['x_local']
        y = cross['y_local']
        x_lambert = cross['x_lambert']
        y_lambert = cross['y_lambert']
        
        # Taille de la croix (10m)
        cross_size = 10
        
        x_coords.append(x)
        y_coords.append(y)
        
        # Dessiner une croix +
        try:
            msp.add_line(
                (x - cross_size, y),
                (x + cross_size, y),
                dxfattribs={'layer': 'LAMBERT_CROSS'}
            )
            msp.add_line(
                (x, y - cross_size),
                (x, y + cross_size),
                dxfattribs={'layer': 'LAMBERT_CROSS'}
            )
            
            # Petit cercle au centre
            msp.add_circle(
                (x, y),
                radius=cross_size / 5,
                dxfattribs={'layer': 'LAMBERT_CROSS'}
            )
            
            entity_count += 3
            
            # Texte avec coordonnées Lambert
            # Format: X=535754.840 / Y=381098.626
            text_height = 2.5
            
            msp.add_text(
                f"X={x_lambert:.3f}",
                dxfattribs={
                    'layer': 'LAMBERT_TEXT',
                    'height': text_height,
                    'style': 'LABELS'
                }
            ).set_placement((x + cross_size + 2, y + 2))
            
            msp.add_text(
                f"Y={y_lambert:.3f}",
                dxfattribs={
                    'layer': 'LAMBERT_TEXT',
                    'height': text_height,
                    'style': 'LABELS'
                }
            ).set_placement((x + cross_size + 2, y - text_height - 1))
            
            entity_count += 2
            
        except Exception as e:
            print(f"  Erreur croix Lambert: {e}")
    
    # ===== METTRE À JOUR LES EXTENTS =====
    if x_coords and y_coords:
        x_min, x_max = min(x_coords), max(x_coords)
        y_min, y_max = min(y_coords), max(y_coords)
        
        # Ajouter des points aux coins pour forcer les extents
        # Ces points seront sur un calque invisible
        try:
            bounds_layer = doc.layers.add('_BOUNDS')
            bounds_layer.off()  # Invisible
        except:
            pass
        
        msp.add_point((x_min, y_min), dxfattribs={'layer': '_BOUNDS'})
        msp.add_point((x_max, y_max), dxfattribs={'layer': '_BOUNDS'})
        
        # Mettre à jour headers
        try:
            doc.header['$EXTMIN'] = (x_min, y_min, 0)
            doc.header['$EXTMAX'] = (x_max, y_max, 0)
            doc.header['$LIMMIN'] = (x_min, y_min)
            doc.header['$LIMMAX'] = (x_max, y_max)
        except:
            pass
        
        print(f"  Extents: ({x_min:.0f}, {y_min:.0f}) à ({x_max:.0f}, {y_max:.0f})")
    
    # Sauvegarder
    doc.saveas(filepath)
    
    # Post-traitement: corriger les EXTENTS manuellement
    if x_coords and y_coords:
        fix_dxf_extents(filepath, x_min, y_min, x_max, y_max)
    
    return entity_count


def fix_dxf_extents(filepath, x_min, y_min, x_max, y_max):
    """
    Corrige les valeurs EXTMIN/EXTMAX dans le fichier DXF.
    ezdxf ne les met pas à jour correctement pour tous les formats.
    """
    try:
        with open(filepath, 'r', encoding='utf-8', errors='ignore') as f:
            content = f.read()
        
        # Remplacer EXTMIN
        import re
        
        # Pattern pour EXTMIN (10\n1e+20\n 20\n1e+20\n 30\n1e+20)
        pattern_extmin = r'(\$EXTMIN\n\s*10\n)[^\n]+(\n\s*20\n)[^\n]+(\n\s*30\n)[^\n]+'
        replacement_extmin = f'\\g<1>{x_min}\\g<2>{y_min}\\g<3>0'
        content = re.sub(pattern_extmin, replacement_extmin, content)
        
        # Pattern pour EXTMAX
        pattern_extmax = r'(\$EXTMAX\n\s*10\n)[^\n]+(\n\s*20\n)[^\n]+(\n\s*30\n)[^\n]+'
        replacement_extmax = f'\\g<1>{x_max}\\g<2>{y_max}\\g<3>0'
        content = re.sub(pattern_extmax, replacement_extmax, content)
        
        # Pattern pour LIMMIN
        pattern_limmin = r'(\$LIMMIN\n\s*10\n)[^\n]+(\n\s*20\n)[^\n]+'
        replacement_limmin = f'\\g<1>{x_min}\\g<2>{y_min}'
        content = re.sub(pattern_limmin, replacement_limmin, content)
        
        # Pattern pour LIMMAX
        pattern_limmax = r'(\$LIMMAX\n\s*10\n)[^\n]+(\n\s*20\n)[^\n]+'
        replacement_limmax = f'\\g<1>{x_max}\\g<2>{y_max}'
        content = re.sub(pattern_limmax, replacement_limmax, content)
        
        with open(filepath, 'w', encoding='utf-8') as f:
            f.write(content)
        
        print("  ✓ Extents corrigés")
    except Exception as e:
        print(f"  ⚠ Erreur correction extents: {e}")

# ============================================================
# ROUTES FLASK
# ============================================================

@app.route('/')
def landing():
    """Page d'accueil publique"""
    user = get_current_user()
    return render_template('landing.html', user=user)

@app.route('/login', methods=['GET', 'POST'])
def login():
    """Page de connexion"""
    if request.method == 'POST':
        username = request.form.get('username', '').strip()
        password = request.form.get('password', '')
        
        conn = get_db()
        user = conn.execute(
            'SELECT * FROM users WHERE username = ? AND password = ?',
            (username, hash_password(password))
        ).fetchone()
        conn.close()
        
        if user:
            session['user_id'] = user['id']
            session['username'] = user['username']
            session['plan'] = user['plan']
            flash(f'Bienvenue {username}!', 'success')
            return redirect(url_for('map_app'))
        else:
            flash('Identifiants incorrects', 'error')
    
    return render_template('login.html')

@app.route('/register', methods=['GET', 'POST'])
def register():
    """Page d'inscription"""
    if request.method == 'POST':
        username = request.form.get('username', '').strip()
        password = request.form.get('password', '')
        email = request.form.get('email', '')
        
        if len(username) < 3 or len(password) < 4:
            flash('Username (3+ chars) et password (4+ chars) requis', 'error')
            return render_template('register.html')
        
        conn = get_db()
        try:
            conn.execute(
                'INSERT INTO users (username, password, email, plan) VALUES (?, ?, ?, ?)',
                (username, hash_password(password), email, 'free')
            )
            conn.commit()
            flash('Compte créé! Connectez-vous.', 'success')
            return redirect(url_for('login'))
        except sqlite3.IntegrityError:
            flash('Ce nom d\'utilisateur existe déjà', 'error')
        finally:
            conn.close()
    
    return render_template('register.html')

@app.route('/logout')
def logout():
    """Déconnexion"""
    session.clear()
    flash('Déconnexion réussie', 'success')
    return redirect(url_for('landing'))

@app.route('/app')
@login_required
def map_app():
    """Application carte (protégée)"""
    user = get_current_user()
    return render_template('index.html', user=user)

@app.route('/pricing')
def pricing():
    """Page des tarifs"""
    user = get_current_user()
    return render_template('pricing.html', user=user)

@app.route('/about')
def about():
    """Page à propos"""
    user = get_current_user()
    return render_template('about.html', user=user)

@app.route('/mapplus')
@login_required
def mapplus():
    """Map Plus - Export avec maquette professionnelle"""
    user = get_current_user()
    return render_template('mapplus.html', user=user)

@app.route('/mapplus3')
@login_required
def mapplus3():
    """Map Plus 3 - Tracés suivant la route, saisie en tableau, couleurs par tracé"""
    user = get_current_user()
    return render_template('mapplus3.html', user=user)

@app.route('/dashboard')
@login_required
def dashboard():
    """Tableau de bord utilisateur"""
    user = get_current_user()
    conn = get_db()
    exports = conn.execute(
        'SELECT * FROM exports WHERE user_id = ? ORDER BY created_at DESC LIMIT 10',
        (session['user_id'],)
    ).fetchall()
    conn.close()
    return render_template('dashboard.html', user=user, exports=exports)

@app.route('/convert')
def convert_page():
    """Page de conversion de coordonnées GPS <-> Lambert"""
    return render_template('convert.html')

@app.route('/api/convert-lambert', methods=['POST'])
def convert_lambert():
    """API pour convertir WGS84 vers Lambert (calcul précis côté serveur)"""
    data = request.get_json()
    lon = data.get('lon')
    lat = data.get('lat')
    
    if lon is None or lat is None:
        return jsonify({'error': 'lon et lat requis'}), 400
    
    transformer = get_lambert_transformer()
    x, y = transformer.transform(lon, lat)
    
    return jsonify({
        'x': round(x, 3),
        'y': round(y, 3),
        'lon': lon,
        'lat': lat
    })

@app.route('/api/convert-to-gps', methods=['POST'])
def convert_to_gps():
    """API pour convertir Lambert Zone I Maroc vers WGS84 (sens inverse)"""
    data = request.get_json()
    x = data.get('x')
    y = data.get('y')
    
    if x is None or y is None:
        return jsonify({'error': 'x et y requis'}), 400
    
    transformer = Transformer.from_crs(
        LAMBERT_MAROC_ZONE1,
        "EPSG:4326",
        always_xy=True
    )
    lon, lat = transformer.transform(x, y)
    
    return jsonify({
        'lon': round(lon, 6),
        'lat': round(lat, 6),
        'x': x,
        'y': y
    })

@app.route('/api/distance-lambert', methods=['POST'])
def distance_lambert():
    """Calcule la distance entre deux points en coordonnées Lambert"""
    data = request.get_json()
    points = data.get('points', [])
    
    if len(points) < 2:
        return jsonify({'error': 'Au moins 2 points requis'}), 400
    
    transformer = get_lambert_transformer()
    
    # Convertir tous les points
    lambert_points = []
    for p in points:
        x, y = transformer.transform(p['lon'], p['lat'])
        lambert_points.append({'x': x, 'y': y, 'lon': p['lon'], 'lat': p['lat']})
    
    # Calculer les distances
    distances = []
    total = 0
    for i in range(1, len(lambert_points)):
        dx = lambert_points[i]['x'] - lambert_points[i-1]['x']
        dy = lambert_points[i]['y'] - lambert_points[i-1]['y']
        dist = (dx**2 + dy**2) ** 0.5
        distances.append({
            'from': i,
            'to': i+1,
            'distance': round(dist, 2)
        })
        total += dist
    
    # Distance directe premier -> dernier
    if len(lambert_points) > 2:
        dx = lambert_points[-1]['x'] - lambert_points[0]['x']
        dy = lambert_points[-1]['y'] - lambert_points[0]['y']
        direct = (dx**2 + dy**2) ** 0.5
    else:
        direct = distances[0]['distance'] if distances else 0
    
    return jsonify({
        'points': lambert_points,
        'distances': distances,
        'total': round(total, 2),
        'direct': round(direct, 2)
    })

@app.route('/api/download', methods=['POST'])
def download_data():
    """Point d'entrée principal pour l'export"""
    try:
        start_time = time.time()
        data = request.get_json()
        
        bbox = data.get('bbox')
        layers = data.get('layers', ['contours', 'roads', 'buildings'])
        mode = data.get('mode', '2d')
        contour_interval = data.get('contour_interval', 10)
        custom_points = data.get('custom_points', [])  # Points de relevé personnalisés
        
        print(f"\n{'='*50}")
        print(f"EXPORT {mode.upper()}")
        print(f"Couches: {', '.join(layers)}")
        print(f"Intervalle: {contour_interval}m")
        if custom_points:
            print(f"Points de relevé: {len(custom_points)}")
        print(f"{'='*50}")
        
        if not bbox or len(bbox) != 4:
            return jsonify({'error': 'bbox requise'}), 400
        
        south, west, north, east = bbox
        print(f"Zone: {south:.4f}, {west:.4f} à {north:.4f}, {east:.4f}")
        
        # Créer le transformer pour projection locale
        transformer = get_local_projection(bbox)
        
        # Collecter toutes les données
        all_data = {
            'contours': [],
            'roads': [],
            'buildings': [],
            'water': [],
            'landuse': []
        }
        
        # ===== COURBES DE NIVEAU =====
        if 'contours' in layers:
            print("\n[1] Génération courbes de niveau...")
            try:
                elevation_grid, lats, lons, source = get_elevation_data(bbox, resolution=40)
                print(f"  Élévation: {elevation_grid.min():.0f}m - {elevation_grid.max():.0f}m ({source})")
                
                contours = generate_contours(
                    bbox, elevation_grid, lats, lons,
                    interval=contour_interval,
                    transformer=transformer
                )
                all_data['contours'] = contours
                print(f"  → {len(contours)} courbes générées")
            except Exception as e:
                print(f"  Erreur: {e}")
                traceback.print_exc()
        
        # ===== DONNÉES OSM =====
        osm_layers = [l for l in layers if l != 'contours']
        
        for layer_name in osm_layers:
            print(f"\n[OSM] {layer_name}...")
            try:
                elements = fetch_osm_data(bbox, layer_name)
                
                # Convertir en coordonnées locales
                local_elements = []
                for el in elements:
                    local_coords = []
                    for lon, lat in el['coords']:
                        x, y = transformer.transform(lon, lat)
                        local_coords.append((round(x, 2), round(y, 2)))
                    
                    # Places (points) n'ont qu'une coordonnée
                    min_coords = 1 if el.get('is_point') or layer_name == 'places' else 2
                    
                    if len(local_coords) >= min_coords:
                        local_elements.append({
                            'coords': local_coords,
                            'type': el['type'],
                            'subtype': el.get('subtype', ''),
                            'name': el.get('name', ''),
                            'closed': el.get('closed', False)
                        })
                
                all_data[layer_name] = local_elements
                print(f"  → {len(local_elements)} éléments")
            except Exception as e:
                print(f"  Erreur: {e}")
        
        # ===== CROIX DE CALAGE LAMBERT =====
        print("\n[LAMBERT] Génération croix de calage...")
        try:
            transformer_lambert = get_lambert_transformer()
            
            # Utiliser les points personnalisés si fournis
            if custom_points and len(custom_points) > 0:
                print(f"  → {len(custom_points)} points personnalisés")
                lambert_crosses = []
                for pt in custom_points:
                    # Convertir en coordonnées locales
                    x_local, y_local = transformer.transform(pt['lon'], pt['lat'])
                    lambert_crosses.append({
                        'x_local': round(x_local, 2),
                        'y_local': round(y_local, 2),
                        'x_lambert': pt['x_lambert'],
                        'y_lambert': pt['y_lambert'],
                        'lon': pt['lon'],
                        'lat': pt['lat']
                    })
            else:
                # Générer automatiquement
                lambert_crosses = generate_lambert_crosses(
                    bbox, 
                    transformer, 
                    transformer_lambert,
                    spacing=300  # Croix tous les 300m environ
                )
                print(f"  → {len(lambert_crosses)} croix auto-générées")
            
            all_data['lambert_crosses'] = lambert_crosses
            print(f"  → Total: {len(lambert_crosses)} croix Lambert")
        except Exception as e:
            print(f"  Erreur Lambert: {e}")
            traceback.print_exc()
        
        # Vérifier qu'on a des données
        total_items = sum(len(v) for v in all_data.values())
        if total_items == 0:
            return jsonify({'error': 'Aucune donnée trouvée'}), 404
        
        # ===== CRÉER LE DXF =====
        print(f"\n[EXPORT] Création DXF...")
        
        with tempfile.TemporaryDirectory() as tmpdir:
            dxf_path = os.path.join(tmpdir, 'export.dxf')
            
            entity_count = create_dxf(all_data, dxf_path, mode=mode)
            print(f"  → {entity_count} entités")
            
            # Créer ZIP
            zip_path = os.path.join(tmpdir, 'export.zip')
            with zipfile.ZipFile(zip_path, 'w', zipfile.ZIP_DEFLATED) as zf:
                zf.write(dxf_path, 'export.dxf')
                
                # Info
                n_crosses = len(all_data.get('lambert_crosses', []))
                custom_txt = "Points personnalisés" if custom_points else "Points auto-générés"
                info = f"""CADMAPPER CLONE - EXPORT DXF
============================
Mode: {mode.upper()}
Zone: {south:.5f}, {west:.5f} à {north:.5f}, {east:.5f}
Couches: {', '.join(layers)}
Intervalle contours: {contour_interval}m

Entités: {entity_count}
Généré: {time.strftime('%Y-%m-%d %H:%M')}

COORDONNÉES DANS LE DXF:
Les coordonnées du dessin sont en mètres locaux,
avec origine au centre de la zone sélectionnée.

CROIX DE CALAGE LAMBERT (Maroc Zone I):
{n_crosses} croix de repère avec coordonnées Lambert.
Calques: LAMBERT_CROSS, LAMBERT_TEXT
Utilisez ces croix pour le recalage dans Covadis:
- X = coordonnée Est (m)
- Y = coordonnée Nord (m)
Projection: Lambert Zone I Maroc (Merchich)

NOMS DES RUES:
Les noms des rues sont sur le calque ROAD_LABELS.

UTILISATION COVADIS:
1. Ouvrir le DXF dans AutoCAD
2. Utiliser les croix Lambert pour le recalage
3. Les coordonnées affichées correspondent à Lambert Maroc Zone I
"""
                zf.writestr('INFO.txt', info)
            
            # Lire et envoyer
            with open(zip_path, 'rb') as f:
                zip_data = f.read()
            
            duration = time.time() - start_time
            size_kb = len(zip_data) / 1024
            
            print(f"\n{'='*50}")
            print(f"TERMINÉ en {duration:.1f}s")
            print(f"Taille: {size_kb:.1f} Ko")
            print(f"{'='*50}\n")
            
            return send_file(
                BytesIO(zip_data),
                mimetype='application/zip',
                as_attachment=True,
                download_name='cadmapper_export.zip'
            )
    
    except Exception as e:
        traceback.print_exc()
        return jsonify({'error': str(e)}), 500


# ============================================================
# EXPORT AVEC MAQUETTE (MAP PLUS)
# ============================================================

def create_dxf_with_maquette(data, filepath, cartouche, lambert_extents, show_road_labels=True, before_save=None):
    """
    Crée un fichier DXF en utilisant la MAQUETTE comme base (INTOUCHABLE).
    
    WORKFLOW:
    1. Charge la maquette_base.dxf (cadre + cartouche fixes)
    2. Trouve le rectangle _BOUNDS (zone de dessin)
    3. Transforme les données Lambert pour rentrer dans _BOUNDS
    4. Ajoute les croix de calage avec les VRAIES coordonnées Lambert
    5. L'utilisateur fait le recalage Helmert dans Covadis avec ces croix
    
    IMPORTANT: Après recalage dans Covadis, faire DECOMPOSER pour figer les coordonnées
    avant de déplacer le croquis dans le rectangle de la maquette.
    
    lambert_extents: (x_min, y_min, x_max, y_max) en Lambert Zone I Maroc
    show_road_labels: Si True, affiche les noms de rues (peut être désactivé)
    """
    import math
    import os
    
    # ===== CHARGER LA MAQUETTE (INTOUCHABLE) =====
    maquette_path = os.path.join(os.path.dirname(__file__), 'maquette_base.dxf')
    
    if not os.path.exists(maquette_path):
        print(f"  ERREUR: Maquette non trouvée: {maquette_path}")
        print(f"  Création d'un fichier simple sans maquette...")
        # Fallback: créer un fichier simple
        doc = ezdxf.new('R2004')
    else:
        doc = ezdxf.readfile(maquette_path)
        print(f"  Maquette chargée: {maquette_path}")
    
    msp = doc.modelspace()
    
    # ===== TROUVER LE RECTANGLE _BOUNDS =====
    bounds_min = None
    bounds_max = None
    for entity in msp:
        if entity.dxftype() == 'POINT' and entity.dxf.layer == '_BOUNDS':
            loc = entity.dxf.location
            x, y = loc[0], loc[1]
            if bounds_min is None:
                bounds_min = [x, y]
                bounds_max = [x, y]
            else:
                bounds_min[0] = min(bounds_min[0], x)
                bounds_min[1] = min(bounds_min[1], y)
                bounds_max[0] = max(bounds_max[0], x)
                bounds_max[1] = max(bounds_max[1], y)
    
    if bounds_min is None:
        # Fallback: utiliser des valeurs par défaut
        print("  Points _BOUNDS non trouvés, utilisation valeurs par défaut")
        bounds_min = [-250, -200]
        bounds_max = [500, 450]
    
    # Dimensions zone de dessin dans la maquette
    maq_x_min, maq_y_min = bounds_min
    maq_x_max, maq_y_max = bounds_max
    maq_width = maq_x_max - maq_x_min
    maq_height = maq_y_max - maq_y_min
    maq_center_x = (maq_x_min + maq_x_max) / 2
    maq_center_y = (maq_y_min + maq_y_max) / 2
    
    print(f"  Zone maquette _BOUNDS: ({maq_x_min:.1f}, {maq_y_min:.1f}) à ({maq_x_max:.1f}, {maq_y_max:.1f})")
    print(f"  Taille maquette: {maq_width:.1f} x {maq_height:.1f}")
    
    # Dimensions Lambert
    lam_x_min, lam_y_min, lam_x_max, lam_y_max = lambert_extents
    lam_width = lam_x_max - lam_x_min
    lam_height = lam_y_max - lam_y_min
    lam_center_x = (lam_x_min + lam_x_max) / 2
    lam_center_y = (lam_y_min + lam_y_max) / 2
    
    print(f"  Données Lambert: ({lam_x_min:.0f}, {lam_y_min:.0f}) à ({lam_x_max:.0f}, {lam_y_max:.0f})")
    print(f"  Taille Lambert: {lam_width:.0f} x {lam_height:.0f} m")
    
    # ===== COORDONNÉES LAMBERT DIRECTES =====
    # Les données sont placées DIRECTEMENT aux coordonnées Lambert réelles
    # Pas de transformation - les coordonnées dans AutoCAD = coordonnées Lambert
    # Cela permet l'utilisation directe sans recalage
    
    scale = 1.0  # ÉCHELLE 1:1 - COORDONNÉES DIRECTES
    
    print(f"  Mode: COORDONNÉES LAMBERT DIRECTES (pas de transformation)")
    
    # ===== FONCTIONS DE TRANSFORMATION =====
    # AUCUNE transformation - coordonnées Lambert directes
    def transform_point(lam_x, lam_y):
        """Retourne les coordonnées Lambert SANS transformation"""
        return (lam_x, lam_y)
    
    def transform_coords(coords):
        """Retourne les coordonnées telles quelles"""
        return [(c[0], c[1]) for c in coords]
    
    # ===== AJOUTER LES CALQUES =====
    layers_to_add = {
        'CONTOUR_MAJOR': 8,
        'CONTOUR_MINOR': 9,
        'ROADS_PRIMARY': 1,
        'ROADS_SECONDARY': 2,
        'ROADS_OTHER': 7,
        'BUILDINGS': 30,
        'WATER': 5,
        'LANDUSE': 3,
        'ROAD_LABELS': 6,
        'PLACES': 6,
        'LAMBERT_CROSS': 200,   # Violet foncé - identifiable
        'LAMBERT_TEXT': 200,    # Violet foncé
        'SEARCH_MARKER': 40,    # Orange - étoile de repérage
    }
    
    for name, color in layers_to_add.items():
        if name not in doc.layers:
            layer = doc.layers.add(name)
            layer.color = color
    
    # Styles de texte
    try:
        if 'LABELS' not in doc.styles:
            doc.styles.add('LABELS', font='Arial')
        if 'PLACES' not in doc.styles:
            doc.styles.add('PLACES', font='Arial')
    except:
        pass
    
    entity_count = 0
    
    # ===== DONNÉES CARTOGRAPHIQUES (TRANSFORMÉES dans la maquette) =====
    
    # Routes
    for item in data.get('roads', []):
        coords = item['coords']  # En Lambert
        subtype = item.get('subtype', 'other')
        road_name = item.get('name', '')
        
        if len(coords) < 2:
            continue
        
        layer = f'ROADS_{subtype.upper()}'
        if layer not in layers_to_add:
            layer = 'ROADS_OTHER'
        
        # Transformer les coordonnées
        transformed = transform_coords(coords)
        msp.add_lwpolyline(transformed, dxfattribs={'layer': layer})
        entity_count += 1
        
        # Nom de la rue (optionnel)
        if show_road_labels and road_name and len(transformed) >= 3:
            mid_idx = len(transformed) // 2
            mid_x, mid_y = transformed[mid_idx]
            
            if mid_idx + 1 < len(transformed):
                dx = transformed[mid_idx + 1][0] - transformed[mid_idx][0]
                dy = transformed[mid_idx + 1][1] - transformed[mid_idx][1]
            else:
                dx = transformed[mid_idx][0] - transformed[mid_idx - 1][0]
                dy = transformed[mid_idx][1] - transformed[mid_idx - 1][1]
            
            angle = math.degrees(math.atan2(dy, dx))
            if angle > 90:
                angle -= 180
            elif angle < -90:
                angle += 180
            
            # Hauteur texte FIXE pour lisibilité (3 unités dans la maquette)
            text_height = 3.0
            
            try:
                msp.add_text(
                    road_name,
                    dxfattribs={
                        'layer': 'ROAD_LABELS',
                        'height': text_height,
                        'rotation': angle,
                        'style': 'LABELS'
                    }
                ).set_placement((mid_x, mid_y))
                entity_count += 1
            except:
                pass
    
    # Bâtiments
    for item in data.get('buildings', []):
        coords = item['coords']
        if len(coords) < 3:
            continue
        transformed = transform_coords(coords)
        msp.add_lwpolyline(transformed, close=True, dxfattribs={'layer': 'BUILDINGS'})
        entity_count += 1
    
    # Eau
    for item in data.get('water', []):
        coords = item['coords']
        closed = item.get('closed', False)
        if len(coords) < 2:
            continue
        transformed = transform_coords(coords)
        msp.add_lwpolyline(transformed, close=closed, dxfattribs={'layer': 'WATER'})
        entity_count += 1
    
    # Contours
    for contour in data.get('contours', []):
        coords = contour['coords']
        is_major = contour['is_major']
        if len(coords) < 2:
            continue
        layer = 'CONTOUR_MAJOR' if is_major else 'CONTOUR_MINOR'
        transformed = transform_coords(coords)
        msp.add_lwpolyline(transformed, dxfattribs={'layer': layer})
        entity_count += 1
    
    # Places (noms de quartiers) - optionnellement affichés avec les labels
    if show_road_labels:  # Même option pour rues et quartiers
        for item in data.get('places', []):
            name = item.get('name', '')
            if not name:
                continue
            
            coords = item['coords']
            if len(coords) < 1:
                continue
            
            transformed = transform_coords(coords)
            x, y = transformed[0]
            
            # Taille FIXE pour lisibilité
            subtype = item.get('subtype', 'locality')
            if subtype in ['town', 'village']:
                text_height = 5.0
            elif subtype in ['suburb', 'quarter']:
                text_height = 4.0
            else:
                text_height = 3.0
            
            try:
                msp.add_text(
                    name.upper(),
                    dxfattribs={
                        'layer': 'PLACES',
                        'height': text_height,
                        'style': 'PLACES'
                    }
                ).set_placement((x, y))
                entity_count += 1
            except:
                pass
    
    # ===== CROIX DE CALAGE - GRILLE UNIFORME - STYLE AXE =====
    # Même nombre de graduations en X et Y
    # Format européen avec virgule comme séparateur décimal
    
    num_divisions = 3  # 3x3 = grille avec 4 divisions = 5 lignes
    
    # Taille des croix proportionnelle à la zone
    axis_length = max(8.0, min(maq_width, maq_height) / 25)  # Longueur de l'axe
    tick_length = axis_length / 4  # Petite marque perpendiculaire
    text_height = max(2.5, axis_length / 4)
    
    def format_coord(value):
        """Formate une coordonnée avec virgule (format européen)
        535500 -> 535,500
        380900 -> 380,900
        """
        # Arrondir à l'entier
        val = int(round(value))
        # Formater avec séparateur de milliers (virgule)
        formatted = f"{val:,}".replace(",", ",")  # 535,500
        return formatted
    
    for cross in data.get('lambert_crosses', []):
        x_lambert = cross['x_lambert']  # Coordonnée VRAIE Lambert
        y_lambert = cross['y_lambert']
        
        # Position TRANSFORMÉE dans la maquette
        tx, ty = transform_point(x_lambert, y_lambert)
        
        try:
            # CROIX EN MODE AXE (style professionnel)
            # Ligne horizontale longue (axe X)
            msp.add_line((tx - axis_length, ty), (tx + axis_length, ty), dxfattribs={'layer': 'LAMBERT_CROSS'})
            # Ligne verticale longue (axe Y)  
            msp.add_line((tx, ty - axis_length), (tx, ty + axis_length), dxfattribs={'layer': 'LAMBERT_CROSS'})
            # Petites marques aux extrémités (style graduation)
            msp.add_line((tx - axis_length, ty - tick_length/2), (tx - axis_length, ty + tick_length/2), dxfattribs={'layer': 'LAMBERT_CROSS'})
            msp.add_line((tx + axis_length, ty - tick_length/2), (tx + axis_length, ty + tick_length/2), dxfattribs={'layer': 'LAMBERT_CROSS'})
            msp.add_line((tx - tick_length/2, ty - axis_length), (tx + tick_length/2, ty - axis_length), dxfattribs={'layer': 'LAMBERT_CROSS'})
            msp.add_line((tx - tick_length/2, ty + axis_length), (tx + tick_length/2, ty + axis_length), dxfattribs={'layer': 'LAMBERT_CROSS'})
            
            # Texte X avec virgule (format européen) - position verticale à gauche
            x_text = format_coord(x_lambert)
            msp.add_text(
                f"X= {x_text}",
                dxfattribs={'layer': 'LAMBERT_TEXT', 'height': text_height, 'rotation': 90, 'style': 'LABELS'}
            ).set_placement((tx - axis_length - text_height - 1, ty))
            
            # Texte Y avec virgule - position horizontale en bas
            y_text = format_coord(y_lambert)
            msp.add_text(
                f"Y= {y_text}",
                dxfattribs={'layer': 'LAMBERT_TEXT', 'height': text_height, 'style': 'LABELS'}
            ).set_placement((tx + 1, ty - axis_length - text_height - 1))
            
            entity_count += 8
        except:
            pass
    
    # ===== TRONÇONS CÂBLES (LIGNES) =====
    troncons = data.get('troncons', [])
    if troncons:
        # Créer le calque pour les câbles s'il n'existe pas
        if 'CABLES' not in doc.layers:
            doc.layers.add('CABLES', color=1)  # Rouge par défaut
        if 'CABLES_TEXT' not in doc.layers:
            doc.layers.add('CABLES_TEXT', color=7)  # Blanc
        
        # Couleurs DXF correspondant aux couleurs web
        color_map = {
            '#ef4444': 1,   # Rouge
            '#f97316': 30,  # Orange
            '#eab308': 2,   # Jaune
            '#22c55e': 3,   # Vert
            '#06b6d4': 4,   # Cyan
            '#3b82f6': 5,   # Bleu
            '#8b5cf6': 6,   # Magenta
            '#d946ef': 201, # Rose
            '#ec4899': 211, # Pink
            '#f43f5e': 11,  # Rouge clair
            '#84cc16': 82,  # Vert lime
            '#14b8a6': 134, # Teal
            '#0ea5e9': 150, # Sky blue
            '#6366f1': 170, # Indigo
            '#a855f7': 200  # Purple
        }
        
        for i, troncon in enumerate(troncons):
            try:
                # Coordonnées Lambert début et arrivée
                x1 = troncon['debut']['x_lambert']
                y1 = troncon['debut']['y_lambert']
                x2 = troncon['arrivee']['x_lambert']
                y2 = troncon['arrivee']['y_lambert']
                
                ml = troncon.get('ml', 0)
                description = troncon.get('description', f'Troncon {i+1}')
                color_hex = troncon.get('color', '#ef4444')
                
                # Convertir couleur hex en couleur DXF
                dxf_color = color_map.get(color_hex, 1 + (i % 7))
                
                # Transformer en position maquette
                tx1, ty1 = transform_point(x1, y1)
                tx2, ty2 = transform_point(x2, y2)
                
                # Dessiner la ligne du tronçon
                msp.add_line(
                    (tx1, ty1), (tx2, ty2),
                    dxfattribs={'layer': 'CABLES', 'color': dxf_color}
                )
                
                # Ajouter cercles aux extrémités
                msp.add_circle((tx1, ty1), radius=2, dxfattribs={'layer': 'CABLES', 'color': dxf_color})
                msp.add_circle((tx2, ty2), radius=2, dxfattribs={'layer': 'CABLES', 'color': dxf_color})
                
                # Calculer le milieu de la ligne pour le texte ML
                mid_x = (tx1 + tx2) / 2
                mid_y = (ty1 + ty2) / 2
                
                # Ajouter le texte ML au milieu
                if ml:
                    msp.add_text(
                        f"{ml}m",
                        dxfattribs={'layer': 'CABLES_TEXT', 'height': 3.0, 'color': dxf_color, 'style': 'LABELS'}
                    ).set_placement((mid_x + 1, mid_y + 1))
                
                # ===== NOMS DES POINTS DÉBUT ET ARRIVÉE =====
                # Nom point DÉBUT (ex: "51m-DEB")
                nom_debut = f"{ml}m-DEB" if ml else f"T{i+1}-DEB"
                msp.add_text(
                    nom_debut,
                    dxfattribs={'layer': 'CABLES_TEXT', 'height': 2.0, 'color': 3, 'style': 'LABELS'}  # Vert
                ).set_placement((tx1 + 3, ty1 + 3))
                
                # Nom point ARRIVÉE (ex: "51m-ARR")
                nom_arrivee = f"{ml}m-ARR" if ml else f"T{i+1}-ARR"
                msp.add_text(
                    nom_arrivee,
                    dxfattribs={'layer': 'CABLES_TEXT', 'height': 2.0, 'color': 1, 'style': 'LABELS'}  # Rouge
                ).set_placement((tx2 + 3, ty2 + 3))
                
                entity_count += 6
                print(f"  📡 Tronçon câble: {nom_debut} → {nom_arrivee} ({ml}m) - Couleur {dxf_color}")
                
            except Exception as e:
                print(f"  Erreur tronçon {i}: {e}")
    
    # ===== REMPLIR LE CARTOUCHE DE LA MAQUETTE =====
    # Positions fixes dans le cartouche de la maquette (basé sur maquette_base.dxf)
    # Le cartouche est sur le calque FORMAT
    
    try:
        # Zone Lambert dans le cartouche
        msp.add_text(
            f"Zone Lambert I Maroc",
            dxfattribs={'layer': 'FORMAT', 'height': 3.0}
        ).set_placement((4100, 650))
        
        msp.add_text(
            f"X: {lam_x_min:.0f} à {lam_x_max:.0f}",
            dxfattribs={'layer': 'FORMAT', 'height': 2.5}
        ).set_placement((4100, 635))
        
        msp.add_text(
            f"Y: {lam_y_min:.0f} à {lam_y_max:.0f}",
            dxfattribs={'layer': 'FORMAT', 'height': 2.5}
        ).set_placement((4100, 620))
        
        # Infos du cartouche éditable
        if cartouche.get('organisme'):
            msp.add_text(
                cartouche['organisme'][:50],
                dxfattribs={'layer': 'FORMAT', 'height': 4.0}
            ).set_placement((4200, 750))
        
        if cartouche.get('travaux'):
            msp.add_text(
                cartouche['travaux'][:60],
                dxfattribs={'layer': 'FORMAT', 'height': 3.0}
            ).set_placement((4200, 700))
        
        if cartouche.get('echelle'):
            msp.add_text(
                f"Échelle: {cartouche['echelle']}",
                dxfattribs={'layer': 'FORMAT', 'height': 3.0}
            ).set_placement((4400, 250))
        
        if cartouche.get('date'):
            msp.add_text(
                f"Date: {cartouche['date']}",
                dxfattribs={'layer': 'FORMAT', 'height': 2.5}
            ).set_placement((4400, 230))
        
        entity_count += 8
    except Exception as e:
        print(f"  Note cartouche: {e}")
    
    if before_save:
        before_save(doc)
    
    # Sauvegarder
    doc.saveas(filepath)
    
    print(f"  → {entity_count} entités ajoutées à la maquette")
    print(f"  → Données transformées dans le rectangle _BOUNDS")
    print(f"  → Croix de calage avec coordonnées Lambert VRAIES")
    print(f"  → Prêt pour recalage Helmert dans Covadis")
    
    return entity_count


# Ancienne fonction maintenue pour compatibilité
def create_dxf_with_template(data, filepath, cartouche):
    """
    Crée un fichier DXF avec maquette professionnelle.
    Les coordonnées sont directement en Lambert Zone I Maroc.
    Inclut le cartouche avec toutes les infos éditables.
    """
    import math
    
    doc = ezdxf.new('R2004')
    msp = doc.modelspace()
    
    # Créer les calques
    layers_info = {
        'CONTOUR_MAJOR': 8,
        'CONTOUR_MINOR': 9,
        'ROADS_PRIMARY': 1,
        'ROADS_SECONDARY': 2,
        'ROADS_OTHER': 7,
        'BUILDINGS': 30,
        'WATER': 5,
        'LANDUSE': 3,
        'ROAD_LABELS': 6,
        'PLACES': 6,              # Magenta pour noms de quartiers
        'LAMBERT_CROSS': 4,
        'LAMBERT_TEXT': 4,
        'CARTOUCHE': 7,           # Blanc pour les lignes du cartouche
        'CARTOUCHE_TEXT': 7,      # Blanc pour texte normal
        'CARTOUCHE_TITLE': 6,     # Magenta pour titres
    }
    
    for name, color in layers_info.items():
        layer = doc.layers.add(name)
        layer.color = color
    
    # Style de texte
    try:
        doc.styles.add('LABELS', font='Arial')
        doc.styles.add('CARTOUCHE', font='Arial')
        doc.styles.add('PLACES', font='Arial')
    except:
        pass
    
    entity_count = 0
    x_coords = []
    y_coords = []
    
    # ===== DONNÉES CARTOGRAPHIQUES (en Lambert) =====
    
    # Routes
    for item in data.get('roads', []):
        coords = item['coords']  # Déjà en Lambert!
        subtype = item.get('subtype', 'other')
        road_name = item.get('name', '')
        
        if len(coords) < 2:
            continue
        
        layer = f'ROADS_{subtype.upper()}'
        if layer not in layers_info:
            layer = 'ROADS_OTHER'
        
        for c in coords:
            x_coords.append(c[0])
            y_coords.append(c[1])
        
        msp.add_lwpolyline(coords, dxfattribs={'layer': layer})
        entity_count += 1
        
        # Nom de la rue
        if road_name and len(coords) >= 3:
            mid_idx = len(coords) // 2
            mid_x, mid_y = coords[mid_idx]
            
            if mid_idx + 1 < len(coords):
                dx = coords[mid_idx + 1][0] - coords[mid_idx][0]
                dy = coords[mid_idx + 1][1] - coords[mid_idx][1]
            else:
                dx = coords[mid_idx][0] - coords[mid_idx - 1][0]
                dy = coords[mid_idx][1] - coords[mid_idx - 1][1]
            
            angle = math.degrees(math.atan2(dy, dx))
            if angle > 90:
                angle -= 180
            elif angle < -90:
                angle += 180
            
            try:
                msp.add_text(
                    road_name,
                    dxfattribs={
                        'layer': 'ROAD_LABELS',
                        'height': 5.0,  # Plus grand pour Lambert
                        'rotation': angle,
                        'style': 'LABELS'
                    }
                ).set_placement((mid_x, mid_y))
                entity_count += 1
            except:
                pass
    
    # Bâtiments
    for item in data.get('buildings', []):
        coords = item['coords']
        if len(coords) < 3:
            continue
        for c in coords:
            x_coords.append(c[0])
            y_coords.append(c[1])
        msp.add_lwpolyline(coords, close=True, dxfattribs={'layer': 'BUILDINGS'})
        entity_count += 1
    
    # Eau
    for item in data.get('water', []):
        coords = item['coords']
        closed = item.get('closed', False)
        if len(coords) < 2:
            continue
        for c in coords:
            x_coords.append(c[0])
            y_coords.append(c[1])
        msp.add_lwpolyline(coords, close=closed, dxfattribs={'layer': 'WATER'})
        entity_count += 1
    
    # Contours
    for contour in data.get('contours', []):
        coords = contour['coords']
        is_major = contour['is_major']
        if len(coords) < 2:
            continue
        layer = 'CONTOUR_MAJOR' if is_major else 'CONTOUR_MINOR'
        for c in coords:
            x_coords.append(c[0])
            y_coords.append(c[1])
        msp.add_lwpolyline(coords, dxfattribs={'layer': layer})
        entity_count += 1
    
    # ===== NOMS DES QUARTIERS/LIEUX =====
    for item in data.get('places', []):
        name = item.get('name', '')
        if not name:
            continue
        
        coords = item['coords']
        if len(coords) < 1:
            continue
        
        x, y = coords[0]
        x_coords.append(x)
        y_coords.append(y)
        
        # Taille du texte selon le type de lieu (plus grand pour Lambert)
        subtype = item.get('subtype', 'locality')
        if subtype in ['town', 'village']:
            text_height = 15.0
        elif subtype in ['suburb', 'quarter']:
            text_height = 12.0
        else:
            text_height = 8.0
        
        try:
            msp.add_text(
                name.upper(),
                dxfattribs={
                    'layer': 'PLACES',
                    'height': text_height,
                    'style': 'PLACES'
                }
            ).set_placement((x, y))
            entity_count += 1
        except:
            pass
    
    # ===== CROIX DE CALAGE =====
    for cross in data.get('lambert_crosses', []):
        x = cross['x_lambert']
        y = cross['y_lambert']
        
        cross_size = 20  # Plus grand pour Lambert (20m)
        
        x_coords.append(x)
        y_coords.append(y)
        
        try:
            # Croix
            msp.add_line((x - cross_size, y), (x + cross_size, y), dxfattribs={'layer': 'LAMBERT_CROSS'})
            msp.add_line((x, y - cross_size), (x, y + cross_size), dxfattribs={'layer': 'LAMBERT_CROSS'})
            msp.add_circle((x, y), radius=cross_size / 4, dxfattribs={'layer': 'LAMBERT_CROSS'})
            
            # Texte coordonnées
            msp.add_text(
                f"X= {x:.0f}",
                dxfattribs={'layer': 'LAMBERT_TEXT', 'height': 4.0, 'style': 'LABELS'}
            ).set_placement((x + cross_size + 3, y + 3))
            
            msp.add_text(
                f"Y= {y:.0f}",
                dxfattribs={'layer': 'LAMBERT_TEXT', 'height': 4.0, 'style': 'LABELS'}
            ).set_placement((x + cross_size + 3, y - 6))
            
            entity_count += 5
        except:
            pass
    
    # ===== CALCULER LA BBOX DU DESSIN =====
    if not x_coords or not y_coords:
        return entity_count
    
    draw_x_min, draw_x_max = min(x_coords), max(x_coords)
    draw_y_min, draw_y_max = min(y_coords), max(y_coords)
    draw_width = draw_x_max - draw_x_min
    draw_height = draw_y_max - draw_y_min
    
    # ===== CARTOUCHE =====
    # Positionner le cartouche en bas à gauche du dessin
    cart_width = 200   # Largeur du cartouche
    cart_height = 120  # Hauteur du cartouche
    cart_x = draw_x_min - cart_width - 50  # À gauche du dessin
    cart_y = draw_y_min - 20  # En bas
    
    # Mettre à jour les coords pour inclure le cartouche
    x_coords.extend([cart_x, cart_x + cart_width])
    y_coords.extend([cart_y, cart_y + cart_height])
    
    try:
        # Cadre extérieur du cartouche
        msp.add_lwpolyline([
            (cart_x, cart_y),
            (cart_x + cart_width, cart_y),
            (cart_x + cart_width, cart_y + cart_height),
            (cart_x, cart_y + cart_height),
            (cart_x, cart_y)
        ], dxfattribs={'layer': 'CARTOUCHE'})
        
        # Ligne séparatrice en-tête
        msp.add_line(
            (cart_x, cart_y + cart_height - 30),
            (cart_x + cart_width, cart_y + cart_height - 30),
            dxfattribs={'layer': 'CARTOUCHE'}
        )
        
        # En-tête - Organisme
        msp.add_text(
            cartouche.get('organisme', 'ROYAUME DU MAROC')[:50],
            dxfattribs={'layer': 'CARTOUCHE_TEXT', 'height': 3.5, 'style': 'CARTOUCHE'}
        ).set_placement((cart_x + cart_width/2, cart_y + cart_height - 10), align=ezdxf.enums.TextEntityAlignment.CENTER)
        
        # Direction
        msp.add_text(
            cartouche.get('direction', '')[:50],
            dxfattribs={'layer': 'CARTOUCHE_TITLE', 'height': 4.0, 'style': 'CARTOUCHE'}
        ).set_placement((cart_x + cart_width/2, cart_y + cart_height - 20), align=ezdxf.enums.TextEntityAlignment.CENTER)
        
        # Séparateur après travaux
        msp.add_line(
            (cart_x, cart_y + cart_height - 50),
            (cart_x + cart_width, cart_y + cart_height - 50),
            dxfattribs={'layer': 'CARTOUCHE'}
        )
        
        # Travaux
        travaux = cartouche.get('travaux', '')
        if travaux:
            msp.add_text(
                travaux[:60],
                dxfattribs={'layer': 'CARTOUCHE_TITLE', 'height': 2.5, 'style': 'CARTOUCHE'}
            ).set_placement((cart_x + cart_width/2, cart_y + cart_height - 40), align=ezdxf.enums.TextEntityAlignment.CENTER)
        
        # Type de plan
        msp.add_text(
            cartouche.get('typePlan', 'PLAN DE RECOLLEMENT'),
            dxfattribs={'layer': 'CARTOUCHE_TITLE', 'height': 4.0, 'style': 'CARTOUCHE'}
        ).set_placement((cart_x + cart_width/2, cart_y + cart_height - 60), align=ezdxf.enums.TextEntityAlignment.CENTER)
        
        # Tronçon
        msp.add_text(
            f"TRONCON: {cartouche.get('troncon', '')}",
            dxfattribs={'layer': 'CARTOUCHE_TEXT', 'height': 3.0, 'style': 'CARTOUCHE'}
        ).set_placement((cart_x + cart_width/2, cart_y + cart_height - 70), align=ezdxf.enums.TextEntityAlignment.CENTER)
        
        # GC
        gc = cartouche.get('gc', '')
        if gc:
            msp.add_text(
                gc[:50],
                dxfattribs={'layer': 'CARTOUCHE_TITLE', 'height': 3.0, 'style': 'CARTOUCHE'}
            ).set_placement((cart_x + cart_width/2, cart_y + cart_height - 80), align=ezdxf.enums.TextEntityAlignment.CENTER)
        
        # Ligne bas
        msp.add_line(
            (cart_x, cart_y + 30),
            (cart_x + cart_width, cart_y + 30),
            dxfattribs={'layer': 'CARTOUCHE'}
        )
        
        # Infos bas - gauche
        msp.add_text(
            f"Société: {cartouche.get('societe', '')}",
            dxfattribs={'layer': 'CARTOUCHE_TEXT', 'height': 2.5, 'style': 'CARTOUCHE'}
        ).set_placement((cart_x + 5, cart_y + 22))
        
        msp.add_text(
            f"Levé par: {cartouche.get('leve', '')}",
            dxfattribs={'layer': 'CARTOUCHE_TEXT', 'height': 2.0, 'style': 'CARTOUCHE'}
        ).set_placement((cart_x + 5, cart_y + 15))
        
        msp.add_text(
            f"Vérifié: {cartouche.get('verifie', '')}",
            dxfattribs={'layer': 'CARTOUCHE_TEXT', 'height': 2.0, 'style': 'CARTOUCHE'}
        ).set_placement((cart_x + 5, cart_y + 8))
        
        # Infos bas - droite
        msp.add_text(
            f"Date: {cartouche.get('date', '')}",
            dxfattribs={'layer': 'CARTOUCHE_TEXT', 'height': 2.5, 'style': 'CARTOUCHE'}
        ).set_placement((cart_x + cart_width - 60, cart_y + 22))
        
        msp.add_text(
            f"Échelle: {cartouche.get('echelle', '1/2000')}",
            dxfattribs={'layer': 'CARTOUCHE_TEXT', 'height': 2.5, 'style': 'CARTOUCHE'}
        ).set_placement((cart_x + cart_width - 60, cart_y + 15))
        
        msp.add_text(
            f"N° Plan: {cartouche.get('numPlan', '1/1')}",
            dxfattribs={'layer': 'CARTOUCHE_TEXT', 'height': 2.5, 'style': 'CARTOUCHE'}
        ).set_placement((cart_x + cart_width - 60, cart_y + 8))
        
        entity_count += 20
        
    except Exception as e:
        print(f"  Erreur cartouche: {e}")
    
    # ===== EXTENTS =====
    if x_coords and y_coords:
        x_min, x_max = min(x_coords), max(x_coords)
        y_min, y_max = min(y_coords), max(y_coords)
        
        try:
            bounds_layer = doc.layers.add('_BOUNDS')
            bounds_layer.off()
        except:
            pass
        
        msp.add_point((x_min, y_min), dxfattribs={'layer': '_BOUNDS'})
        msp.add_point((x_max, y_max), dxfattribs={'layer': '_BOUNDS'})
        
        try:
            doc.header['$EXTMIN'] = (x_min, y_min, 0)
            doc.header['$EXTMAX'] = (x_max, y_max, 0)
            doc.header['$LIMMIN'] = (x_min, y_min)
            doc.header['$LIMMAX'] = (x_max, y_max)
        except:
            pass
        
        print(f"  Lambert Extents: ({x_min:.0f}, {y_min:.0f}) à ({x_max:.0f}, {y_max:.0f})")
    
    doc.saveas(filepath)
    
    if x_coords and y_coords:
        fix_dxf_extents(filepath, x_min, y_min, x_max, y_max)
    
    return entity_count


@app.route('/api/download-with-template', methods=['POST'])
def download_with_template(payload=None, before_save=None):
    """Export avec maquette professionnelle - coordonnées Lambert directes"""
    try:
        start_time = time.time()
        data = payload if payload is not None else request.get_json()
        
        bbox = data.get('bbox')
        layers = data.get('layers', ['roads'])
        contour_interval = data.get('contour_interval', 10)
        cartouche = data.get('cartouche', {})
        show_road_labels = data.get('show_road_labels', True)  # Option noms de rues
        grid_spacing = data.get('grid_spacing', 'auto')  # Espacement graduations
        grid_offset = data.get('grid_offset', 0)  # Offset vertical croix
        grid_mode = data.get('grid_mode', 'full')  # Mode: full, extremities, corners
        troncons = data.get('troncons', [])  # Liste des tronçons câbles
        
        print(f"\n{'='*50}")
        print(f"EXPORT MAP PLUS - AVEC MAQUETTE")
        print(f"Couches: {', '.join(layers)}")
        print(f"Grille: mode={grid_mode}, espacement={grid_spacing}, offset={grid_offset}")
        if troncons:
            print(f"Tronçons câbles: {len(troncons)} ligne(s)")
        print(f"{'='*50}")
        
        if not bbox or len(bbox) != 4:
            return jsonify({'error': 'bbox requise'}), 400
        
        south, west, north, east = bbox
        print(f"Zone: {south:.5f}, {west:.5f} à {north:.5f}, {east:.5f}")
        
        # Transformer DIRECTEMENT en Lambert (pas en local)
        transformer_lambert = get_lambert_transformer()
        
        # Collecter les données
        all_data = {
            'contours': [],
            'roads': [],
            'buildings': [],
            'water': [],
            'landuse': [],
            'places': [],
            'lambert_crosses': []
        }
        
        # ===== DONNÉES OSM =====
        for layer_name in layers:
            if layer_name == 'contours':
                continue
            
            print(f"\n[OSM] {layer_name}...")
            try:
                elements = fetch_osm_data(bbox, layer_name)
                
                # Convertir directement en LAMBERT (pas en local!)
                lambert_elements = []
                road_names_done = set()
                
                for el in elements:
                    lambert_coords = []
                    for lon, lat in el['coords']:
                        x, y = transformer_lambert.transform(lon, lat)
                        lambert_coords.append((round(x, 2), round(y, 2)))
                    
                    # Places (points) n'ont qu'une coordonnée
                    min_coords = 1 if el.get('is_point') or layer_name == 'places' else 2
                    
                    if len(lambert_coords) >= min_coords:
                        name = el.get('name', '')
                        # Éviter les noms de rue en double
                        if layer_name == 'roads' and name:
                            if name in road_names_done:
                                name = ''
                            else:
                                road_names_done.add(name)
                        
                        lambert_elements.append({
                            'coords': lambert_coords,
                            'type': el['type'],
                            'subtype': el.get('subtype', ''),
                            'name': name,
                            'closed': el.get('closed', False)
                        })
                
                all_data[layer_name] = lambert_elements
                print(f"  → {len(lambert_elements)} éléments en Lambert")
            except Exception as e:
                print(f"  Erreur: {e}")
        
        # ===== CONTOURS EN LAMBERT =====
        if 'contours' in layers:
            print("\n[CONTOURS] Génération...")
            try:
                elevation_grid, lats, lons, source = get_elevation_data(bbox, resolution=40)
                
                # Générer les contours et convertir en Lambert
                import matplotlib
                matplotlib.use('Agg')
                import matplotlib.pyplot as plt
                
                z_min = elevation_grid.min()
                z_max = elevation_grid.max()
                levels = np.arange(
                    np.floor(z_min / contour_interval) * contour_interval,
                    np.ceil(z_max / contour_interval) * contour_interval + contour_interval,
                    contour_interval
                )
                
                fig, ax = plt.subplots()
                X, Y = np.meshgrid(lons, lats)
                cs = ax.contour(X, Y, elevation_grid, levels=levels)
                plt.close(fig)
                
                contour_lines = []
                for level_idx, level in enumerate(cs.levels):
                    is_major = int(level) % 50 == 0
                    try:
                        if hasattr(cs, 'allsegs') and level_idx < len(cs.allsegs):
                            for segment in cs.allsegs[level_idx]:
                                if len(segment) >= 2:
                                    lambert_coords = []
                                    for point in segment:
                                        lon, lat = point[0], point[1]
                                        x, y = transformer_lambert.transform(lon, lat)
                                        lambert_coords.append((round(x, 2), round(y, 2)))
                                    
                                    if len(lambert_coords) >= 2:
                                        contour_lines.append({
                                            'coords': lambert_coords,
                                            'elevation': float(level),
                                            'is_major': is_major
                                        })
                    except:
                        pass
                
                all_data['contours'] = contour_lines
                print(f"  → {len(contour_lines)} courbes en Lambert")
            except Exception as e:
                print(f"  Erreur contours: {e}")
        
        # ===== CROIX DE CALAGE LAMBERT =====
        print("\n[CROSSES] Génération grille de repères...")
        print(f"  Espacement: {grid_spacing}, Offset Y: {grid_offset}m")
        
        # Calculer les coins en Lambert
        x_sw, y_sw = transformer_lambert.transform(west, south)
        x_ne, y_ne = transformer_lambert.transform(east, north)
        
        # Calculer l'espacement
        zone_width = x_ne - x_sw
        zone_height = y_ne - y_sw
        
        if grid_spacing == 'auto':
            # Espacement automatique selon la taille de la zone
            if max(zone_width, zone_height) < 200:
                spacing = 50
            elif max(zone_width, zone_height) < 500:
                spacing = 100
            elif max(zone_width, zone_height) < 1000:
                spacing = 200
            else:
                spacing = 500
        else:
            spacing = int(grid_spacing)
        
        print(f"  Mode: {grid_mode}, Espacement: {spacing}m")
        
        lambert_crosses = []
        
        if grid_mode == 'corners':
            # 4 coins uniquement
            lambert_crosses = [
                {'x_lambert': round(x_sw, 0), 'y_lambert': round(y_sw, 0)},
                {'x_lambert': round(x_ne, 0), 'y_lambert': round(y_sw, 0)},
                {'x_lambert': round(x_sw, 0), 'y_lambert': round(y_ne, 0)},
                {'x_lambert': round(x_ne, 0), 'y_lambert': round(y_ne, 0)},
            ]
            
        elif grid_mode == 'extremities':
            # Grille uniquement sur les bords (première ligne de croix autour du cadre)
            # Utilise l'espacement choisi pour placer des croix le long des 4 bords
            
            # Points de départ proches des bords réels
            x_start = math.ceil(x_sw / spacing) * spacing
            x_end = math.floor(x_ne / spacing) * spacing
            y_start = math.ceil(y_sw / spacing) * spacing
            y_end = math.floor(y_ne / spacing) * spacing
            
            # Si les points arrondis sont trop loin des bords, ajuster
            if x_start - x_sw > spacing * 0.5:
                x_start = x_sw
            if x_ne - x_end > spacing * 0.5:
                x_end = x_ne
            if y_start - y_sw > spacing * 0.5:
                y_start = y_sw
            if y_ne - y_end > spacing * 0.5:
                y_end = y_ne
            
            added = set()  # Pour éviter les doublons
            
            # Bord Sud (y proche de y_sw)
            x = x_start
            while x <= x_end:
                key = (round(x, 0), round(y_sw, 0))
                if key not in added:
                    lambert_crosses.append({'x_lambert': key[0], 'y_lambert': key[1]})
                    added.add(key)
                x += spacing
            
            # Bord Nord (y proche de y_ne)
            x = x_start
            while x <= x_end:
                key = (round(x, 0), round(y_ne, 0))
                if key not in added:
                    lambert_crosses.append({'x_lambert': key[0], 'y_lambert': key[1]})
                    added.add(key)
                x += spacing
            
            # Bord Ouest (x proche de x_sw)
            y = y_start
            while y <= y_end:
                key = (round(x_sw, 0), round(y, 0))
                if key not in added:
                    lambert_crosses.append({'x_lambert': key[0], 'y_lambert': key[1]})
                    added.add(key)
                y += spacing
            
            # Bord Est (x proche de x_ne)
            y = y_start
            while y <= y_end:
                key = (round(x_ne, 0), round(y, 0))
                if key not in added:
                    lambert_crosses.append({'x_lambert': key[0], 'y_lambert': key[1]})
                    added.add(key)
                y += spacing
            
            # Ajouter les 4 coins exacts si pas déjà présents
            corners = [
                (round(x_sw, 0), round(y_sw, 0)),
                (round(x_ne, 0), round(y_sw, 0)),
                (round(x_sw, 0), round(y_ne, 0)),
                (round(x_ne, 0), round(y_ne, 0)),
            ]
            for key in corners:
                if key not in added:
                    lambert_crosses.append({'x_lambert': key[0], 'y_lambert': key[1]})
                    added.add(key)
            
        else:
            # Grille complète (mode 'full')
            # Arrondir les limites aux multiples de l'espacement
            x_start = math.floor(x_sw / spacing) * spacing
            x_end = math.ceil(x_ne / spacing) * spacing
            y_start = math.floor(y_sw / spacing) * spacing
            y_end = math.ceil(y_ne / spacing) * spacing
            
            # Appliquer l'offset vertical
            y_offset = grid_offset
            
            x = x_start
            while x <= x_end:
                y = y_start + y_offset
                while y <= y_end + abs(y_offset):
                    # Vérifier si le point est dans la zone (avec marge)
                    if (x_sw - spacing/2 <= x <= x_ne + spacing/2 and 
                        y_sw - spacing/2 <= y <= y_ne + spacing/2):
                        lambert_crosses.append({
                            'x_lambert': round(x, 0),
                            'y_lambert': round(y, 0)
                        })
                    y += spacing
                x += spacing
            
            # Limiter le nombre de croix
            if len(lambert_crosses) > 200:
                step = len(lambert_crosses) // 200 + 1
                lambert_crosses = lambert_crosses[::step]
        
        all_data['lambert_crosses'] = lambert_crosses
        print(f"  → {len(lambert_crosses)} croix de repère")
        
        # ===== TRONÇONS CÂBLES (LIGNES) =====
        troncons = data.get('troncons', [])
        all_data['troncons'] = []
        if troncons and len(troncons) > 0:
            print(f"\n[TRONÇONS] Ajout de {len(troncons)} tronçon(s) câbles")
            for i, troncon in enumerate(troncons):
                debut = troncon.get('debut', {})
                arrivee = troncon.get('arrivee', {})
                description = troncon.get('description', f'Tronçon {i+1}')
                ml = troncon.get('ml', 0)
                color = troncon.get('color', '#ef4444')
                
                debut_lat = debut.get('lat')
                debut_lon = debut.get('lon')
                arrivee_lat = arrivee.get('lat')
                arrivee_lon = arrivee.get('lon')
                
                if debut_lat and debut_lon and arrivee_lat and arrivee_lon:
                    # Coordonnées Lambert début
                    x1 = debut.get('x')
                    y1 = debut.get('y')
                    if not x1 or not y1 or x1 == 0 or y1 == 0:
                        x1, y1 = transformer_lambert.transform(debut_lon, debut_lat)
                    
                    # Coordonnées Lambert arrivée
                    x2 = arrivee.get('x')
                    y2 = arrivee.get('y')
                    if not x2 or not y2 or x2 == 0 or y2 == 0:
                        x2, y2 = transformer_lambert.transform(arrivee_lon, arrivee_lat)
                    
                    all_data['troncons'].append({
                        'debut': {'x_lambert': round(x1, 2), 'y_lambert': round(y1, 2)},
                        'arrivee': {'x_lambert': round(x2, 2), 'y_lambert': round(y2, 2)},
                        'description': description,
                        'ml': ml,
                        'color': color
                    })
                    print(f"  📡 {description}: {ml}m - ({x1:.0f},{y1:.0f}) → ({x2:.0f},{y2:.0f})")
        
        # ===== CALCULER LES EXTENTS LAMBERT =====
        all_x = []
        all_y = []
        
        # Collecter toutes les coordonnées Lambert
        for item in all_data.get('roads', []):
            for c in item['coords']:
                all_x.append(c[0])
                all_y.append(c[1])
        
        for item in all_data.get('buildings', []):
            for c in item['coords']:
                all_x.append(c[0])
                all_y.append(c[1])
        
        for item in all_data.get('water', []):
            for c in item['coords']:
                all_x.append(c[0])
                all_y.append(c[1])
        
        for contour in all_data.get('contours', []):
            for c in contour['coords']:
                all_x.append(c[0])
                all_y.append(c[1])
        
        for cross in lambert_crosses:
            all_x.append(cross['x_lambert'])
            all_y.append(cross['y_lambert'])
        
        if all_x and all_y:
            lambert_extents = (min(all_x), min(all_y), max(all_x), max(all_y))
        else:
            # Fallback aux coins de la zone
            lambert_extents = (x_sw, y_sw, x_ne, y_ne)
        
        print(f"  Extents Lambert: X={lambert_extents[0]:.0f}-{lambert_extents[2]:.0f}, Y={lambert_extents[1]:.0f}-{lambert_extents[3]:.0f}")
        
        # ===== CRÉER LE DXF AVEC MAQUETTE =====
        print("\n[EXPORT] Création DXF avec maquette...")
        print(f"  Afficher noms de rues: {show_road_labels}")
        
        with tempfile.TemporaryDirectory() as tmpdir:
            dxf_path = os.path.join(tmpdir, 'export_maquette.dxf')
            
            # Utiliser la nouvelle fonction avec maquette
            entity_count = create_dxf_with_maquette(all_data, dxf_path, cartouche, lambert_extents, show_road_labels, before_save)
            print(f"  → {entity_count} entités")
            
            # ZIP
            zip_path = os.path.join(tmpdir, 'export.zip')
            with zipfile.ZipFile(zip_path, 'w', zipfile.ZIP_DEFLATED) as zf:
                zf.write(dxf_path, 'plan_avec_maquette.dxf')
                
                info = f"""HYPERYSCO-MAP PLUS - EXPORT AVEC MAQUETTE
==========================================

Ce DXF contient:
- Les données cartographiques en COORDONNÉES LAMBERT ZONE I MAROC
- Le cartouche professionnel intégré
- Les croix de repères avec coordonnées Lambert

AUCUN RECALAGE COVADIS NÉCESSAIRE !

Ouvrez directement dans AutoCAD et utilisez tel quel.

Infos du cartouche:
- Organisme: {cartouche.get('organisme', '-')}
- Direction: {cartouche.get('direction', '-')}
- Type: {cartouche.get('typePlan', '-')}
- Société: {cartouche.get('societe', '-')}
- Échelle: {cartouche.get('echelle', '1/2000')}
- Date: {cartouche.get('date', '-')}

Généré le: {time.strftime('%Y-%m-%d %H:%M')}
Par: Hyperysco-Map Plus
"""
                zf.writestr('INFO.txt', info)
            
            with open(zip_path, 'rb') as f:
                zip_data = f.read()
            
            duration = time.time() - start_time
            print(f"\n{'='*50}")
            print(f"MAP PLUS TERMINÉ en {duration:.1f}s")
            print(f"{'='*50}\n")
            
            return send_file(
                BytesIO(zip_data),
                mimetype='application/zip',
                as_attachment=True,
                download_name='hyperysco_maquette.zip'
            )
    
    except Exception as e:
        traceback.print_exc()
        return jsonify({'error': str(e)}), 500


# ============================================================
# MAP PLUS 3 - ITINÉRAIRES ET TRACÉS COLORÉS
# ============================================================

OSRM_SERVERS = {
    'driving': [
        "https://router.project-osrm.org/route/v1/driving",
        "https://routing.openstreetmap.de/routed-car/route/v1/driving",
    ],
    'foot': [
        "https://routing.openstreetmap.de/routed-foot/route/v1/driving",
    ],
}

MAPPLUS3_ACI = {
    '#ef4444': 1,   # Rouge
    '#f97316': 30,  # Orange
    '#eab308': 2,   # Jaune
    '#84cc16': 82,  # Vert lime
    '#14b8a6': 134, # Turquoise
    '#06b6d4': 4,   # Cyan
    '#0ea5e9': 150, # Bleu ciel
    '#6366f1': 170, # Indigo
    '#8b5cf6': 6,   # Violet
    '#a855f7': 200, # Pourpre
    '#d946ef': 201, # Fuchsia
    '#ec4899': 211, # Rose
    '#ffffff': 7,   # Blanc / Noir
    '#22c55e': 3,   # Vert
    '#3b82f6': 5,   # Bleu
}

ACI_DEPART = 5   # Bleu
ACI_ARRIVEE = 3  # Vert


@app.route('/api/route', methods=['POST'])
def route_between_points():
    """Itinéraire routier passant par les points donnés (A, [étapes], B)"""
    data = request.get_json() or {}
    points = data.get('points', [])
    profile = data.get('profile', 'driving')

    if len(points) < 2:
        return jsonify({'error': 'Au moins 2 points requis'}), 400
    if len(points) > 25:
        # Garder départ, arrivée et des étapes réparties
        step = (len(points) - 1) / 24
        points = [points[round(i * step)] for i in range(25)]

    coords = ';'.join(f"{float(p['lon']):.6f},{float(p['lat']):.6f}" for p in points)

    for server in OSRM_SERVERS.get(profile, OSRM_SERVERS['driving']):
        try:
            response = requests.get(
                f"{server}/{coords}",
                params={'overview': 'full', 'geometries': 'geojson'},
                headers=OVERPASS_HEADERS,
                timeout=30
            )
            if response.status_code != 200:
                print(f"    OSRM {server} -> HTTP {response.status_code}")
                continue
            result = response.json()
            if result.get('code') != 'Ok' or not result.get('routes'):
                continue
            route = result['routes'][0]
            path = [[lat, lon] for lon, lat in route['geometry']['coordinates']]
            return jsonify({'path': path, 'distance': route.get('distance', 0)})
        except Exception as e:
            print(f"    OSRM {server} -> erreur {e}")

    return jsonify({'error': 'Aucun itinéraire trouvé entre ces points'}), 502


def _point_along(coords, ratio):
    """Point situé à `ratio` de la longueur d'une polyligne"""
    lengths = [math.dist(coords[i - 1], coords[i]) for i in range(1, len(coords))]
    target = sum(lengths) * ratio
    for i, seg in enumerate(lengths):
        if target <= seg and seg > 0:
            t = target / seg
            (x1, y1), (x2, y2) = coords[i], coords[i + 1]
            return (x1 + (x2 - x1) * t, y1 + (y2 - y1) * t)
        target -= seg
    return coords[-1]


def add_mapplus3_troncons(doc, troncons, transformer_lambert):
    """Ajoute les tracés (chemin complet, couleur choisie, départ bleu / arrivée vert)"""
    msp = doc.modelspace()

    for name, color in (('CABLES', 1), ('CABLES_TEXT', 7), ('CABLES_DEPART', ACI_DEPART), ('CABLES_ARRIVEE', ACI_ARRIVEE)):
        if name not in doc.layers:
            doc.layers.add(name, color=color)

    count = 0
    for i, troncon in enumerate(troncons):
        try:
            path = troncon.get('path') or [troncon['debut'], troncon['arrivee']]
            coords = [transformer_lambert.transform(p['lon'], p['lat']) for p in path]
            coords = [(round(x, 2), round(y, 2)) for x, y in coords]
            if len(coords) < 2:
                continue

            ml = troncon.get('ml', 0)
            color_hex = str(troncon.get('color', '#ef4444')).lower()
            attribs = {'layer': 'CABLES'}
            if color_hex in MAPPLUS3_ACI:
                attribs['color'] = MAPPLUS3_ACI[color_hex]
            else:
                rgb = tuple(int(color_hex[k:k + 2], 16) for k in (1, 3, 5))
                attribs['true_color'] = dxf_colors.rgb2int(rgb)

            msp.add_lwpolyline(coords, dxfattribs=attribs)

            (x1, y1), (x2, y2) = coords[0], coords[-1]
            for (x, y), layer, aci in (((x1, y1), 'CABLES_DEPART', ACI_DEPART), ((x2, y2), 'CABLES_ARRIVEE', ACI_ARRIVEE)):
                msp.add_circle((x, y), radius=2, dxfattribs={'layer': layer, 'color': aci})
                hatch = msp.add_hatch(color=aci, dxfattribs={'layer': layer})
                hatch.paths.add_edge_path().add_arc((x, y), radius=2, start_angle=0, end_angle=360)

            if ml:
                mid_x, mid_y = _point_along(coords, 0.5)
                text_attribs = {'layer': 'CABLES_TEXT', 'height': 3.0, 'style': 'LABELS'}
                text_attribs.update({k: v for k, v in attribs.items() if k != 'layer'})
                msp.add_text(f"{ml}m", dxfattribs=text_attribs).set_placement((mid_x + 1, mid_y + 1))

            nom_debut = f"{ml}m-DEB" if ml else f"T{i+1}-DEB"
            nom_arrivee = f"{ml}m-ARR" if ml else f"T{i+1}-ARR"
            msp.add_text(
                nom_debut,
                dxfattribs={'layer': 'CABLES_TEXT', 'height': 2.0, 'color': ACI_DEPART, 'style': 'LABELS'}
            ).set_placement((x1 + 3, y1 + 3))
            msp.add_text(
                nom_arrivee,
                dxfattribs={'layer': 'CABLES_TEXT', 'height': 2.0, 'color': ACI_ARRIVEE, 'style': 'LABELS'}
            ).set_placement((x2 + 3, y2 + 3))

            count += 1
            print(f"  📡 Tracé {nom_debut} → {nom_arrivee}: {len(coords)} points, couleur {color_hex}")
        except Exception as e:
            print(f"  Erreur tracé {i}: {e}")

    return count


@app.route('/api/download-mapplus3', methods=['POST'])
def download_mapplus3():
    """Export Map Plus 3 : maquette Map Plus + tracés avec chemin complet et couleurs"""
    try:
        data = request.get_json() or {}
        troncons = data.get('troncons', [])
        transformer_lambert = get_lambert_transformer()

        def add_traces(doc):
            if troncons:
                print(f"\n[MAP PLUS 3] Ajout de {len(troncons)} tracé(s)")
                add_mapplus3_troncons(doc, troncons, transformer_lambert)

        return download_with_template(dict(data, troncons=[]), before_save=add_traces)

    except Exception as e:
        traceback.print_exc()
        return jsonify({'error': f"{type(e).__name__}: {e}"}), 500


# ============================================================
# MAIN
# ============================================================

if __name__ == '__main__':
    print("""
╔═══════════════════════════════════════════════════════════╗
║                                                           ║
║      ██╗  ██╗██╗   ██╗██████╗ ███████╗██████╗ ██╗   ██╗  ║
║      ██║  ██║╚██╗ ██╔╝██╔══██╗██╔════╝██╔══██╗╚██╗ ██╔╝  ║
║      ███████║ ╚████╔╝ ██████╔╝█████╗  ██████╔╝ ╚████╔╝   ║
║      ██╔══██║  ╚██╔╝  ██╔═══╝ ██╔══╝  ██╔══██╗  ╚██╔╝    ║
║      ██║  ██║   ██║   ██║     ███████╗██║  ██║   ██║     ║
║      ╚═╝  ╚═╝   ╚═╝   ╚═╝     ╚══════╝╚═╝  ╚═╝   ╚═╝     ║
║                                                           ║
║                    HYPERYSCO-MAP v1.0                     ║
╠═══════════════════════════════════════════════════════════╣
║  ✓ Export DXF professionnel pour AutoCAD/Covadis          ║
║  ✓ Courbes de niveau (données réelles)                    ║
║  ✓ Routes avec noms de rues                               ║
║  ✓ Croix Lambert Zone I Maroc pour recalage               ║
║  ✓ Points de relevé personnalisés                         ║
╚═══════════════════════════════════════════════════════════╝
    """)
    print("→ Ouvrez http://localhost:5000")
    print("→ Utilisateurs: ELHCH/ELHCH, ACHACH/ACHACH")
    print()
    app.run(host='0.0.0.0', port=5000, debug=True)
