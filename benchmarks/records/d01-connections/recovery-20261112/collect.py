#!/usr/bin/env python3
"""Preserve real checker outputs and verify their source/Git identities."""
import argparse, collections, gzip, hashlib, json, pathlib, shutil, subprocess
ROOT = pathlib.Path(subprocess.check_output(['git','rev-parse','--show-toplevel'], text=True).strip())
OUT = pathlib.Path(__file__).resolve().parent

def digest(data): return hashlib.sha256(data).hexdigest()
def command(*args): return subprocess.check_output(args, cwd=ROOT, text=True).strip()
def save(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2)+'\n')
def gz(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    with gzip.open(path,'wb') as stream: stream.write(data)
def packed(path, value): gz(path,json.dumps(value,ensure_ascii=False).encode())
def tree(commit):
    result={}
    for row in subprocess.check_output(['git','ls-tree','-rz',commit],cwd=ROOT).split(b'\0'):
        if row:
            info,name=row.split(b'\t',1); result[name.decode()]=info.split()[2].decode()
    return result

def identity(snapshot, commit, destination):
    data=json.loads(snapshot.read_bytes()); inventory={}; at_commit=tree(commit); at_head=tree('HEAD')
    for name, source in data['files'].items():
        p=pathlib.Path(name); relative=str(p.relative_to(ROOT)); raw=source.encode()
        assert p.read_bytes()==raw, ('checkout changed',relative)
        blob=hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()
        assert at_commit.get(relative)==blob, ('checked commit mismatch',relative)
        assert at_head.get(relative)==blob, ('current HEAD mismatch',relative)
        inventory[relative]={'sha256':digest(raw),'git_blob':blob}
    packed(destination/'source-files.json.gz',inventory)
    packed(destination/'aliases.json.gz',data.get('aliases',{}))
    return {'source_snapshot_sha256':digest(snapshot.read_bytes()),'source_files':len(inventory),
            'checked_commit':commit,'current_head':command('git','rev-parse','HEAD'),
            'checkout_and_both_git_trees_match':True}

def build():
    destination=OUT/'build'; destination.mkdir(exist_ok=True)
    work=ROOT/'work/d01-recovery'
    build_log=(work/'build.log').read_bytes(); tests=(work/'checkpoint-tests.log').read_bytes()
    assert b'Finished' in build_log
    assert b'test result: ok. 13 passed; 0 failed' in tests
    binary=ROOT/'target/release/cli'; inputs={}; tracked=tree('HEAD')
    for name, blob in tracked.items():
        if (name.startswith('src/') and (name.endswith('.rs') or name.endswith('Cargo.toml'))) or name in ['Cargo.toml','Cargo.lock']:
            raw=(ROOT/name).read_bytes()
            assert hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==blob
            inputs[name]=digest(raw)
    gz(destination/'build.log.gz',build_log); gz(destination/'checkpoint-tests.log.gz',tests)
    packed(destination/'checker-source-sha256.json.gz',inputs)
    save(destination/'summary.json',{'outcome':'accepted','build_exit_code':0,'checkpoint_exit_code':0,
         'checkpoint_tests_passed':13,'commit':command('git','rev-parse','HEAD'),
         'checker_sha256':digest(binary.read_bytes()),'rustc':command('rustc','--version'),
         'cargo':command('cargo','--version'),'checker_source_files':len(inputs),
         'd01_src_tree':command('git','rev-parse','HEAD:libs/geometry/bundle_connections/src'),
         'd01_manifest_blob':command('git','rev-parse','HEAD:libs/geometry/bundle_connections/ref.toml')})
    print('saved build and 13 checkpoint tests')

def driver(name, state, partial):
    index=json.loads((state/'latest.json').read_bytes()); report=pathlib.Path(index['report'])
    raw=report.read_bytes(); r=json.loads(raw); destination=OUT/name; destination.mkdir(exist_ok=True)
    if not partial:
        assert r['outcome']=='accepted',r['outcome']
        assert set(r['verified'])==set(r['targets'])
        assert r['save_failures']==0
    assert digest(pathlib.Path(r['binary']).read_bytes())==r['binary_sha256']
    source=report.parent/'source.json'; ident=identity(source,r['commit'],destination)
    assert ident['source_snapshot_sha256']==r['source_sha256']
    gz(destination/'driver.json.gz',raw)
    workers=[]
    for attempt in r['attempts']:
        p=pathlib.Path(attempt['report'])
        if p.exists():
            body=p.read_bytes(); workers.append({'file':p.name,'sha256':digest(body),'raw_utf8':body.decode()})
        else:
            assert partial, ('missing accepted report',str(p))
            workers.append({'file':p.name,'missing':True})
    packed(destination/'workers.raw.json.gz',workers)
    summary={k:v for k,v in r.items() if k not in ['attempts','targets','verified','newly_checked','reused','package_entries']}
    summary.update(ident)
    summary['counts']={k:len(r[k]) for k in ['targets','verified','newly_checked','reused']}
    summary['attempts']=len(r['attempts']); summary['attempt_outcomes']=dict(collections.Counter(a.get('outcome','unknown') for a in r['attempts']))
    summary['original_report_sha256']=digest(raw); summary['partial_checkpoint']=partial
    save(destination/'summary.json',summary)
    print(name,r['outcome'],summary['counts'])

def cli(name, report, snapshot, commit):
    commit=command('git','rev-parse',commit)
    raw=report.read_bytes(); r=json.loads(raw); assert r['outcome']=='accepted'
    destination=OUT/name; destination.mkdir(exist_ok=True)
    ident=identity(snapshot,commit,destination)
    gz(destination/'report.json.gz',raw)
    save(destination/'summary.json',{'outcome':'accepted','exit_code':0,**ident,
      'checker_sha256':digest((ROOT/'target/release/cli').read_bytes()),
      'verified_modules':len(r.get('verified_modules',[])), 'source_checked_modules':len(r.get('checked_modules',[])),
      'execution':r.get('execution',{}),'storage':r.get('storage',{}),'original_report_sha256':digest(raw)})
    print(name,'accepted',len(r.get('verified_modules',[])))

parser=argparse.ArgumentParser(); parser.add_argument('mode',choices=['build','driver','cli']); parser.add_argument('name',nargs='?'); parser.add_argument('--state',type=pathlib.Path); parser.add_argument('--partial',action='store_true'); parser.add_argument('--report',type=pathlib.Path); parser.add_argument('--snapshot',type=pathlib.Path); parser.add_argument('--commit')
a=parser.parse_args()
if a.mode=='build': build()
elif a.mode=='driver': driver(a.name,a.state,a.partial)
else: cli(a.name,a.report,a.snapshot,a.commit)
