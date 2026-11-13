"""Restore losslessly archived release intermediates from the local manifest."""
import gzip
import hashlib
import json
import os
import shutil
from pathlib import Path

manifest = json.loads((Path(__file__).parent / 'manifest.json').read_text())
for item in manifest['files']:
    target, archive = Path(item['path']), Path(item['archive'])
    if target.exists():
        with target.open('rb') as stream:
            if hashlib.file_digest(stream, 'sha256').hexdigest() != item['sha256']:
                raise RuntimeError(f'refuse to overwrite changed artifact: {target}')
        continue
    if shutil.disk_usage(target.parent).free < item['bytes'] + 512 * 1024**2:
        raise RuntimeError('insufficient free space for lossless restoration')
    temporary = target.with_name(target.name + '.restore-tmp')
    with gzip.open(archive, 'rb') as source, temporary.open('wb') as destination:
        shutil.copyfileobj(source, destination)
    with temporary.open('rb') as stream:
        if hashlib.file_digest(stream, 'sha256').hexdigest() != item['sha256']:
            raise RuntimeError(f'archive checksum mismatch: {archive}')
    os.chmod(temporary, item['mode'])
    os.utime(temporary, ns=(item['mtime_ns'], item['mtime_ns']))
    os.replace(temporary, target)
