import re,sys
names=['executions','futures','outcomes','ub_kinds','future+registers','+memory','+reads','+ub','largest_future','within_rm','within_reads','within_ub']
rows=[]
for line in open(sys.argv[1]):
    f,rest=line.rstrip('\n').split('\t',1)
    if 'NONE' in rest: continue
    vals=[int(x) for x in re.findall(r'=(\d+)',rest)]
    rows.append((f,dict(zip(names,vals))))
T=lambda k:sum(d[k] for _,d in rows)
print('programs',len(rows))
for k in names[:8]: print(f'  {k:18s} {T(k):8d}')
print('programs where the future already separates every execution (future+registers+memory+reads = futures):',sum(d['+reads']==d['futures'] for _,d in rows))
print('programs where registers+memory add classes beyond the future:',sum(d['+memory']>d['futures'] for _,d in rows))
print('programs where reads add classes beyond future+registers+memory:',sum(d['+reads']>d['+memory'] for _,d in rows))
print('largest executions-per-future, max over programs:',max(d['largest_future'] for _,d in rows))
big=sorted(rows,key=lambda x:-x[1]['executions'])[:8]
print(f"  {'exec':>6s} {'fut':>5s} {'outc':>5s} {'f+reg':>6s} {'+mem':>6s} {'+reads':>6s} {'+ub':>6s} {'ub':>3s}")
for f,d in big: print(f"  {d['executions']:6d} {d['futures']:5d} {d['outcomes']:5d} {d['future+registers']:6d} {d['+memory']:6d} {d['+reads']:6d} {d['+ub']:6d} {d['ub_kinds']:3d}  {f}")
