"""
Initialisation de la base de données Hyperysco-map
"""
import sqlite3
import hashlib
import os

DB_PATH = os.path.join(os.path.dirname(__file__), 'hyperysco.db')

def hash_password(password):
    """Hash un mot de passe avec SHA256"""
    return hashlib.sha256(password.encode()).hexdigest()

def init_db():
    """Crée la base de données et les tables"""
    conn = sqlite3.connect(DB_PATH)
    cursor = conn.cursor()
    
    # Table utilisateurs
    cursor.execute('''
        CREATE TABLE IF NOT EXISTS users (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            username TEXT UNIQUE NOT NULL,
            password TEXT NOT NULL,
            email TEXT,
            plan TEXT DEFAULT 'free',
            created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
            exports_count INTEGER DEFAULT 0,
            last_login TIMESTAMP
        )
    ''')
    
    # Table exports (historique)
    cursor.execute('''
        CREATE TABLE IF NOT EXISTS exports (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER,
            bbox TEXT,
            layers TEXT,
            created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
            file_size INTEGER,
            FOREIGN KEY (user_id) REFERENCES users (id)
        )
    ''')
    
    # Table paiements (pour plus tard)
    cursor.execute('''
        CREATE TABLE IF NOT EXISTS payments (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER,
            amount REAL,
            plan TEXT,
            status TEXT DEFAULT 'pending',
            created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
            FOREIGN KEY (user_id) REFERENCES users (id)
        )
    ''')
    
    # Insérer les utilisateurs par défaut
    default_users = [
        ('ELHCH', hash_password('ELHCH'), 'elhch@hyperysco.ma', 'premium'),
        ('ACHACH', hash_password('ACHACH'), 'achach@hyperysco.ma', 'premium'),
        ('admin', hash_password('admin123'), 'admin@hyperysco.ma', 'admin'),
    ]
    
    for user in default_users:
        try:
            cursor.execute('''
                INSERT INTO users (username, password, email, plan) 
                VALUES (?, ?, ?, ?)
            ''', user)
            print(f"✓ Utilisateur créé: {user[0]}")
        except sqlite3.IntegrityError:
            print(f"  Utilisateur existant: {user[0]}")
    
    conn.commit()
    conn.close()
    print(f"\n✓ Base de données initialisée: {DB_PATH}")

if __name__ == '__main__':
    init_db()
