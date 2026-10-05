# Count executions violating case (b): a loop read (thread LT) in iteration i
# reads from a write w on another thread with (e,w) in (dp u rf)+ for some
# LT-event e of an earlier iteration. Iterations: LT events in label order, a
# read of the loop's guard location closes an iteration.
import json,sys
d=json.load(open(sys.argv[1])); LT=1
tot=viol=multi=0; wit=None
for e in d['executions']:
    tot+=1
    ev={x['id']:x for x in e['events']}
    lt=sorted(x['id'] for x in e['events'] if x.get('thread')==LT and x['type'] in 'RWAF')
    rlocs=[ev[i]['location'] for i in lt if ev[i]['type']=='R']
    gl=rlocs[0] if rlocs else None
    # the loop body opens with its guard read
    it={}; k=0
    for i in lt:
        if ev[i]['type']=='R' and ev[i]['location']==gl: k+=1
        it[i]=k
    if k>1: multi+=1
    E=[tuple(p) for p in e['dp']]+[tuple(p) for p in e['rf']]
    succ={}
    for a,b in E: succ.setdefault(a,set()).add(b)
    def reach(s):
        seen=set(); st=[s]
        while st:
            x=st.pop()
            for y in succ.get(x,()):
                if y not in seen: seen.add(y); st.append(y)
        return seen
    bad=None
    for w,r in e['rf']:
        if r in it and ev.get(w,{}).get('thread') not in (LT,None) and ev[w]['type']!='I':
            for x in lt:
                if it[x]<it[r] and w in reach(x):
                    bad=(x,it[x],w,r,it[r]); break
        if bad: break
    if bad:
        viol+=1; wit=wit or (e['id'],bad,e['rf'],e['dp'])
print(f"{sys.argv[1].split('/')[-1]}: {tot} execs, {multi} with >1 iteration, {viol} violate case (b)")
if wit: print("  witness exec %s: earlier-iter event %d (iter %d) reaches w=%d, read %d (iter %d); rf=%s dp=%s"%(wit[0],*wit[1],wit[2],wit[3]))
