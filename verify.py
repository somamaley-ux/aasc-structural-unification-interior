"""Verify the curated export's file hashes without requiring Lean or dependencies."""
from pathlib import Path
import hashlib,json
root=Path(__file__).resolve().parent
manifest=json.loads((root/'metadata/export-files.json').read_text(encoding='utf-8'))
for row in manifest['files']:
 original=root/row['path']; path=original.resolve()
 assert path.is_relative_to(root) and not original.is_symlink(),row['path']
 assert path.is_file(),row['path']
 assert hashlib.sha256(path.read_bytes()).hexdigest()==row['sha256'],row['path']
print('VERIFIED',len(manifest['files']),'curated source, dependency, documentation and evidence files')
