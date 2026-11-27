"""Exact, standard-library reproduction for prescribed terminal curvature in trees.
Run python3 verify.py. Optional: python3 verify.py --word '+--+-' --scale 4.
A + is a log-convex triple (a strict log-concavity failure), at deficit 1 first.
"""
from itertools import product
from math import comb
from collections import deque, Counter
from hashlib import sha256
from argparse import ArgumentParser
import json
import random


def require(condition, message):
    if not condition:
        raise ValueError(message)


def profile(word, small=True):
    require(all(ch in '+-' for ch in word), 'word must be a string of + and -')
    t = len(word) - len(word.lstrip('-'))
    suffix = word[t:]
    h = len(suffix) + 1
    if all(ch == '+' for ch in suffix):
        f = [s*s for s in range(h+1)]
    else:
        u = [sum((j-i)*(1 if suffix[i-1] == '+' else -1) for i in range(2, j))
             for j in range(h+1)]
        def candidate(a):
            return [0] + [a*(2*j-1)+u[j] for j in range(1,h+1)]
        def works(f):
            return (all(f[i] < f[i+1] for i in range(h)) and
                    all(f[i+j] > f[i]+f[j] for i in range(1,h) for j in range(1,h-i+1)))
        if not small:
            v, slope = [0], h
            for j in range(1,h+1):
                v.append(v[-1]+slope)
                if j<h:
                    slope += 1 if suffix[j-1]=='+' else -1
            a = 2*v[h]+1
            f = [0]+[a*(2*j-1)+v[j] for j in range(1,h+1)]
        else:
            a = next(b for b in range(1, 4*h*h+1) if works(candidate(b)))
            f = candidate(a)
        require(works(f), 'invalid superadditive profile')
    b = f[-1]
    weights = [2*b+t-i for i in range(t)]  # 2B+t,...,2B+1
    return f, weights


def predicted(f, weights, r):
    b, t, h = f[-1], len(weights), len(f)-1
    require(0 <= r <= h+t, 'outside profile')
    base = b*h*(h+1) + sum(weights)
    k = max(r-t,0)
    return base + sum(weights[:r]) + b*k + f[k]


def add(*ps):
    return [sum(col) for col in zip(*ps)]


def mul(a,b):
    return [sum(a[i]*b[k-i] for i in range(k+1)) for k in range(len(a))]


def pow_poly(a,n):
    res = [1]+[0]*(len(a)-1)
    while n:
        if n % 2:
            res = mul(res,a)
        n //= 2
        if n:
            a = mul(a,a)
    return res


def binomial(base,n,h):
    return [(comb(n,i)*base**(n-i) if i<=n else 0) for i in range(h+1)]


def shift(a):
    return [0]+a[:-1]


def label_states(outgoing,incoming,h):
    pos = mul(binomial(1,outgoing,h),binomial(2,incoming,h))
    neg = mul(binomial(2,outgoing,h),binomial(1,incoming,h))
    zero = shift(binomial(2,outgoing+incoming,h))
    return pos,neg,zero


def tail_formula(f,weights,p,depth):
    b, h = f[-1], len(f)-1
    branch = label_states(p*b,2*p*b,depth)
    any_branch = add(*branch)
    minus_or_zero = add(*branch[1:])
    root_positive = root_other = [1]+[0]*depth
    for s in range(1,h+1):
        plus,minus,empty = label_states(p*f[s],0,depth)
        general = pow_poly(any_branch,s)
        plus = mul(plus,general)
        minus = mul(minus,pow_poly(minus_or_zero,s))
        empty = mul(empty,general)
        root_positive = mul(root_positive,add(plus,empty))
        root_other = mul(root_other,add(plus,minus,empty))
    for w in weights:
        plus,minus,empty = label_states(p*w,p*w,depth)
        root_positive = mul(root_positive,add(plus,empty))
        root_other = mul(root_other,add(plus,minus,empty))
    return add(root_positive,root_other,shift(root_other))


def parameters(f, weights, p):
    h = len(f)-1
    arms = h*(h+1)//2
    d = 1+h+arms+len(weights)
    w = 3*f[-1]*arms + sum(f) + 2*sum(weights)
    return d,w,d+p*w


def build_core(f,weights):
    # directed edges are stored as (source, target); (out, in) weights per label
    vals, edges = [(0,0)], []
    for s in range(1,len(f)):
        center = len(vals)
        vals.append((f[s],0))
        edges.append((0,center))
        for _ in range(s):
            edges.append((len(vals),center))
            vals.append((f[-1],2*f[-1]))
    for w in weights:
        edges.append((0,len(vals)))
        vals.append((w,w))
    return vals,edges


def expanded(vals, edges, p):
    # Physical, undirected graph. Consecutive vertices (2v,2v+1) are matching pairs.
    nlabels = len(vals)+p*sum(a+b for a,b in vals)
    g = [[] for _ in range(2*nlabels)]
    def link(i,j):
        g[i].append(j)
        g[j].append(i)
    for i in range(nlabels):
        link(2*i,2*i+1)
    for a,b in edges:
        link(2*a,2*b+1)
    leaf = len(vals)
    for v,(outgoing,incoming) in enumerate(vals):
        for _ in range(outgoing*p):
            link(2*v,2*leaf+1)
            leaf += 1
        for _ in range(incoming*p):
            link(2*leaf,2*v+1)
            leaf += 1
    require(leaf == nlabels, 'label count')
    return g


def tail_tree_dp(g,k):
    # Rooted independent-set recurrence on the physical edge list, no matched-pair states.
    parent = [-2]*len(g)
    parent[0] = -1
    order = [0]
    for v in order:
        for u in g[v]:
            if u == parent[v]:
                continue
            require(parent[u] == -2, 'cycle or repeated edge')
            parent[u] = v
            order.append(u)
    require(len(order) == len(g), 'not connected')
    def combine(a,b):
        degree = max(a[0],b[0])
        res = [0]*(k+1)
        for deg,poly in (a,b):
            for i in range(k+1-(degree-deg)):
                res[degree-deg+i] += poly[i]
        return degree,res
    def prod(a,b):
        return a[0]+b[0],mul(a[1],b[1])
    states = {}
    unit = [1]+[0]*k
    for v in reversed(order):
        excluded, included = (0,unit), (1,unit)
        for u in g[v]:
            if parent[u] == v:
                e,i = states.pop(u)
                excluded = prod(excluded,combine(e,i))
                included = prod(included,e)
        states[v] = excluded,included
    return combine(*states[0])


def diameter(g):
    def farthest(start):
        queue = deque([(start,-1,0)])
        while queue:
            v,parent,d = queue.popleft()
            for u in g[v]:
                if u != parent:
                    queue.append((u,v,d+1))
        return v,d
    return farthest(farthest(0)[0])[1]


def direct_subsets(g):
    # Independent-set recursion over labelled subsets, independent of the two polynomial DPs.
    nbr = [sum(1<<u for u in ns) for ns in g]
    ans = [0]*(len(g)+1)
    def visit(remaining,k):
        if remaining == 0:
            ans[k] += 1
            return
        v = remaining & -remaining
        rest = remaining ^ v
        visit(rest,k)
        visit(rest & ~nbr[v.bit_length()-1],k+1)
    visit((1<<len(g))-1,0)
    while ans[-1]==0:
        ans.pop()
    return ans[::-1]


def max_by_enumeration(vals,edges,rmax):
    # -1 = minus, 0 = empty, 1 = plus.
    exact = [-1]*(rmax+1)
    for state in product((-1,0,1),repeat=len(vals)):
        holes = state.count(0)
        if holes>rmax or any(state[a]==1 and state[b]==-1 for a,b in edges):
            continue
        score = sum((a if x==-1 else b if x==1 else a+b) for (a,b),x in zip(vals,state))
        exact[holes] = max(exact[holes],score)
    return [max(exact[:r+1]) for r in range(rmax+1)]


def signs(tail):
    def sign(x):
        return '+' if x>0 else '-' if x<0 else '0'
    return ''.join(sign(a*c-b*b) for a,b,c in zip(tail,tail[1:],tail[2:]))


def trial(word,p,small=True):
    f,weights = profile(word,small)
    a = tail_formula(f,weights,p,len(word)+1)
    d,w,m = parameters(f,weights,p)
    return a,m,signs(a)


def suite():
    rng = random.Random(28112026)
    subset_checks = 0
    for _ in range(65):
        d = rng.randrange(1,6)
        ed = []
        for u in range(1,d):
            v = rng.randrange(u)
            ed.append((u,v) if rng.randrange(2) else (v,u))
        vals = [(0,0) for _ in range(d)]
        for _ in range(rng.randrange(0,9-d)):
            v = rng.randrange(d)
            x,y = vals[v]
            vals[v] = (x+1,y) if rng.randrange(2) else (x,y+1)
        g = expanded(vals,ed,1)
        brute = direct_subsets(g)
        require(brute == tail_tree_dp(g,len(brute)-1)[1], 'subset vs tree DP')
        subset_checks += 1
    full = 0
    for word in ('','+','-','++','+-','-+','--','+++','+-+','--+','++++++'):
        for p in ((1,2) if len(word)<4 else (2,)):
            f,ws = profile(word)
            v,e = build_core(f,ws)
            g = expanded(v,e,p)
            d,w,m = parameters(f,ws,p)
            k = len(word)+1
            degree,coeff = tail_tree_dp(g,k)
            require(degree==m and len(g)==2*m and diameter(g)<=10, 'graph parameters')
            require(all((i^1) in ns for i,ns in enumerate(g)), 'missing matching edge')
            require(coeff==tail_formula(f,ws,p,k), 'expanded-tree vs grouped formula')
            full += 1
    core_cases = 0
    form_states = 0
    for word in ('','+','-','++','+-','-+','--','--+','---'):
        for small in (False,True):
            f,ws = profile(word,small)
            v,e = build_core(f,ws)
            k = len(word)+1
            require(max_by_enumeration(v,e,k)==[predicted(f,ws,r) for r in range(k+1)], 'core maximum')
            core_cases += 1
            form_states += 3**len(v)
    # Edge cases for the star calculation, including equality f(s)=B and unused budgets.
    local = 0
    for s in range(1,10):
        for b in range(1,9):
            for bonus in range(b+1):
                for r in range(s+3):
                    values=[]
                    for t in range(min(s,r)+1):
                        values += [2*b*s+b*t,b*s+2*b*t+bonus]
                        if t+1<=r:
                            values.append(2*b*s+b*t+bonus)
                    require(max(values)==2*b*s+b*min(r,s)+(bonus if r>=s else 0),'star formula')
                    local += 1
    all_words = 0
    scales = Counter()
    mismatches = []
    profile_checks = 0
    for l in range(1,8):
        for chars in product('+-',repeat=l):
            word=''.join(chars)
            for small in (False,True):
                f,ws=profile(word,small)
                ex=[predicted(f,ws,r) for r in range(l+2)]
                got=''.join('+' if a+c>2*b else '-' if a+c<2*b else '0' for a,b,c in zip(ex,ex[1:],ex[2:]))
                require(got==word,'signed exponent test')
                d,w,m=parameters(f,ws,128*(l+1)**2)
                require((2**d*m**(l+1))**2 < 2**(128*(l+1)**2),'uniform scale')
                profile_checks += 1
            for p in (1,2,3,4,6,8,12,16,24,32,64):
                _,_,obs=trial(word,p)
                if p==1 and obs!=word:
                    mismatches.append((word,obs))
                if obs==word:
                    scales[p]+=1
                    break
            else:
                raise ValueError('failed to find witness for '+word)
            all_words+=1
    require(mismatches,'missing negative control')
    examples=[]
    for word in ('+','+-+-','---+--','++++++','++++++++'):
        for p in (1,2,3,4,6,8,12,16,24,32):
            a,m,s=trial(word,p)
            if s==word:
                f,ws=profile(word)
                v,e=build_core(f,ws)
                g=expanded(v,e,p)
                deg,physical=tail_tree_dp(g,len(word)+1)
                require(deg==m and physical==a and diameter(g)<=10, 'expanded example')
                full += 1
                # Digest uses a length-delimited unsigned big-endian encoding.
                digest=sha256()
                for n in a:
                    z=n.to_bytes((n.bit_length()+7)//8,'big')
                    digest.update(len(z).to_bytes(8,'big')+z)
                examples.append({'word':word,'scale':p,'vertices':2*m,'alpha':m,
                                 'tail_bits':[n.bit_length() for n in a],
                                 'sha256':digest.hexdigest()})
                break
        else:
            raise ValueError('missing example')
    return {'subset_checks':subset_checks,'expanded_graph_cross_checks':full,
            'exhaustive_core_cases':core_cases,'core_assignments_scanned':form_states,
            'local_star_cases':local,'sign_words':all_words,'exact_exponent_and_scale_checks':profile_checks,'first_tested_successful_scale':dict(sorted(scales.items())),
            'scale_one_failures':len(mismatches),'negative_control':mismatches[0], 'examples':examples}


if __name__=='__main__':
    parser=ArgumentParser(description=__doc__)
    parser.add_argument('--word',default=None)
    parser.add_argument('--scale',default=2,type=int)
    args=parser.parse_args()
    if args.word is None:
        print(json.dumps(suite(),indent=2))
    else:
        require(args.scale>=1,'positive scale required')
        a,m,s=trial(args.word,args.scale)
        print(json.dumps({'word':args.word,'observed':s,'vertices':2*m,'alpha':m,
                          'tail_in_hex':[hex(x) for x in a]},indent=2))
