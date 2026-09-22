import re,sys,collections
rows={}
for line in open(sys.argv[1]):
    f,rest=line.rstrip('\n').split('\t',1)
    d=rows.setdefault(f,{})
    if rest.startswith('S14 stages'):
        m=re.search(r'all=(\d+) dedup_fr=(\d+) min_fr=(\d+) dedup_ex=(\d+) min_ex=(\d+) coherent=(\d+)',rest)
        d['stages']=tuple(map(int,m.groups()))
    else:
        for k,v in re.findall(r'(\w+)=(\d+)',rest): d[k]=int(v)
corp=lambda f:f.split('/')[0]
print('programs',len(rows))
print('max futures per combination, any program:',max(d['max_futures_per_combo'] for d in rows.values()))
print('programs with only_true>0 (true future not in unminimised set):',sum(d['only_true']>0 for d in rows.values()))
lost=[(f,d) for f,d in rows.items() if d['only_nomin']>0]
print('programs where the unminimised witness set has futures the tool does not report:',len(lost))
stage_names=['dedup_fr','min_fr','dedup_ex','min_ex','coherence']
by_stage=collections.Counter(); futs_lost=collections.Counter()
for f,d in rows.items():
    s=d['stages']
    for i,n in enumerate(stage_names):
        drop=s[i]-s[i+1]
        if drop>0: by_stage[n]+=1; futs_lost[n]+=drop
print('programs losing futures at each stage:',dict(by_stage))
print('futures lost at each stage (sum):',dict(futs_lost))
print('total futures: unminimised',sum(d['futures_nomin'] for d in rows.values()),'reported',sum(d['futures_true'] for d in rows.values()))
cc=[(f,d) for f,d in rows.items() if d['combos_valid']>d['combos_coherent']]
print('programs with a combination that has valid but no coherent execution:',len(cc), ' combos:',sum(d['combos_valid']-d['combos_coherent'] for f,d in cc),'of',sum(d['combos_valid'] for d in rows.values()))
fv=[(f,d) for f,d in rows.items() if d['futures_valid']>d['futures_nomin']]
print('programs where coherence removes a whole future (valid>coherent futures):',len(fv))
print()
print('per corpus: programs / with minimality loss / futures unminimised->reported')
pc=collections.defaultdict(lambda:[0,0,0,0])
for f,d in rows.items():
    c=pc[corp(f)]; c[0]+=1; c[1]+=d['only_nomin']>0; c[2]+=d['futures_nomin']; c[3]+=d['futures_true']
for k,v in sorted(pc.items()): print(f'  {k:28s} {v[0]:4d} {v[1]:4d} {v[2]:7d} -> {v[3]:7d}')
print()
print('largest losses:')
for f,d in sorted(lost,key=lambda x:-x[1]['only_nomin'])[:12]:
    print(f"  {d['futures_nomin']:6d} -> {d['futures_true']:6d}  combos {d['combos_valid']:6d}  {f}")
print()
print('coherence-caveat programs:')
for f,d in sorted(cc,key=lambda x:-(x[1]['combos_valid']-x[1]['combos_coherent']))[:12]:
    print(f"  combos valid {d['combos_valid']:5d} coherent {d['combos_coherent']:5d}  futures valid {d['futures_valid']} coherent {d['futures_nomin']} reported {d['futures_true']}  {f}")
