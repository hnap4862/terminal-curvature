"""Check actual integer coefficients at the uniform scale of the theorem."""
import json
from math import comb
from verify import (build_core, diameter, expanded, parameters, predicted, profile,
                    require, signs, tail_formula, tail_tree_dp)


def main():
    records = []
    for word in ('+', '-', '++', '+-', '-+', '--', '---', '++++', '-'*16):
        h = len(word)+1
        p = 128*h*h
        f,ws = profile(word, small=False)
        d,w,m = parameters(f,ws,p)
        a = tail_formula(f,ws,p,h)
        require(signs(a) == word, 'certified-scale sign')
        for r,n in enumerate(a):
            k = p*predicted(f,ws,r)
            require((1<<k) <= n <= (comb(m,r) << (d+k)), 'coefficient outside envelope')
        cross_checked = False
        if 2*m <= 100000:
            vals,edges = build_core(f,ws)
            tree = expanded(vals,edges,p)
            degree, other = tail_tree_dp(tree,h)
            require(degree==m and other==a and diameter(tree)<=10,'expanded graph at uniform scale')
            cross_checked = True
        records.append(dict(word=word,scale=p,vertices=2*m,maximum_coefficient_bits=max(x.bit_length() for x in a),
                            expanded_graph_cross_check=cross_checked))
    print(json.dumps(records, indent=2))


if __name__=='__main__':
    main()
