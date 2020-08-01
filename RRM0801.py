######
# 8.1 multi flow with function mapping
# get_route -> every possible routes for each flow
# get_mapping -> mapping SFC to every possible route (length>=T+2)
######

from z3 import *
import time
import random

# define global variables
N = 100
F = 3 # number of flow
S = [50,6,87]
D = [0,2,43]
B_sfc = [20,20,10] # service function chian Brandwidth
B_node = 3 # max number of flow on one node
L = 6 # max route Length
T = 4 # number of functions
c = [10,10,10,10] # service function CPU requirement

# load topology
def load_edges(file):
    edges = {} 
    B = {}
    topo = [] # topo[i] concludes the nodes connected to node i
    with open(file) as f:
        datas = f.readlines()
  
    for d in datas:
        d = d.split()
        d = [int(x) for x in d]
        if d[0] in edges:
            edges[d[0]].append(d[1:])
        else:
            edges[d[0]] = [d[1:]]
        
    i = 0
    keys = list(edges.keys())
    keys.sort()
    for key in keys:
        while(i!= key):
            i = i+1
            topo.append([])
        topo.append([j[0] for j in edges[key]])
        B[key] = [j[1] for j in edges[key]]
        i = i+1

    print('===Loaded topology with '+str(len(topo))+' nodes===')
    return topo,B

# sum of outcoming edges (z3 variable)
def edges_out(E,i,f):
    outs = [E[f][i][j] for j in range(len(edges[i]))]
    return Sum(outs)

# sum of incoming edges (z3)
def edges_in(E,i,f):
    in_nodes = search_in(i)
    if in_nodes:
        ins = [E[f][node[0]][node[1]] for node in in_nodes]
        y = Sum(ins)
    else:
        y = 0
    return y

# sum of flows coming into a node
def edges_node(E,i):
    nodes = []
    for f in range(F):
        outs = [E[f][i][j] for j in range(len(edges[i]))]
        nodes+=outs
    return Sum(nodes)

# find incoming edges to node i
def search_in(i):
    nodes = []
    for j in range(len(edges)):
        e = edges[j]
        for k in range(len(e)):
            if e[k]==i:
                nodes.append([j,k])
    return nodes

# find Brandwith for edges in route
def search_b(route):
    b_nodes = []
    for i in range(len(route)-1):
        node = route[i]
        nex = route[i+1]
        index = edges[node].index(nex)
        b = B[node][index]
        b_nodes.append(b)
    return b_nodes

# generate available route
def get_solver():
    solver = Solver()
    constrains = []
    # generate edges in z3 variables

    E = [] #E:[f_1,f_2...f_F] f:[[u01,u02],[u11,u12]...]
    for f in range(F):
        flow = []
        for i in range(N):
            tmp = []
            count = 0
            for e in edges[i]:
                name = 'u_'+str(f)+'_'+str(i)+'_'+str(e)
                tmp.append(Int(name))
                edge = tmp[count]
                cons = Or(edge==1,edge==0)
                constrains.append(cons)
                count = count + 1
            flow.append(tmp)
        E.append(flow)
    
    for f in range(F):
        # cons: incoming equals outcoming
        for i in range(N):
            if (i != S[f] and i != D[f]):
                x = edges_out(E,i,f)# O_i
                y = edges_in(E,i,f) # I_i
                # incoming == outcoming
                cons = x==y 
                constrains.append(cons)
                # ensure everytime generate one flow
                cons = Or(x==1,x==0) 
                constrains.append(cons)
                # cons5: node CPU constraint
                z = edges_node(E,i)
                cons = z<=B_node
                constrains.append(cons)

        # cons: only 1 route comes out from Source
        x = edges_out(E,S[f],f)
        cons = x==1
        constrains.append(cons)

        # cons: only 1 route comes inro from Source
        y = edges_in(E,D[f],f)
        cons = y==1
        constrains.append(cons)

        # cons: length constraint
        ls = [E[f][i][count] for i in range(N) for count in range(len(edges[i]))]
        length = Sum(ls)
        cons = length<=L
        constrains.append(cons)
        cons = length>=T+2
        constrains.append(cons)

    solver.add(constrains)
    return solver

# map service functions to nodes except S & D
def get_mapping(routes):
    import numpy as np
    routes = np.array(routes) 

    log('Mapping')
    for f in range(F):
        # choose viable routes with T function node besides S&D
        route = routes[:,f]
        route = np.unique(route)
        log('##Mapping flow: %d' %(f+1))
        log('#Source node: '+str(S[f]))
        log('#Destination node: '+str(D[f]))
        if len(route) == 0:
            log('##No mapping solution!')
        for r in route:
            if r == []:
                continue
            log('##Selected route: '+str(r))
            B_edges = search_b(r)
            l = len(r)-2
            # generate nodes (components) mapping in z3 variables
            b = [[Int('b_'+str(i)+str(j)) for j in range(T)] for i in range(l)]

            solver = Solver()
            for bi in b:
                for i in bi:
                    solver.append(Or(i==0,i==1))

            # cons1: one function
            for j in range(T):
                funcs = []
                for i in range(l):
                    funcs.append(b[i][j])
                solver.append(Sum(funcs)==1)

            # cons2: service sequence
            for t in range(T):
                funcs = []
                for j in range(T):
                    func = []
                    for i in range(t+1):
                        func.append(b[i][j])
                    funcs.append(Sum(func))
                for k in range(T-1):
                    solver.append(funcs[k]>=funcs[k+1])

            for i in range(l):
                # cons3: CPU stress
                resource = [b[i][j]*c[j] for j in range(T)]
                solver.append(Sum(resource)<=C[i])

                # cons4: brandwidth
                solver.append(B_sfc[f]<=B_edges[i])

            count = 0
            while(solver.check()==sat):
                log('#Mapping %d:' %(count+1))
                count = count + 1
                m = solver.model()
                mapping = {}
                cons = []
                for d in m.decls():
                    if m[d]==1:
                        # print("{}".format(d.name()),end=', ')
                        i = d.name().split('_')[1][0]
                        j = d.name().split('_')[1][1]
                        mapping[j] = i
                        # no repeating
                        cons.append(d()==0)
                solver.append(Or(cons))
                for k in sorted(mapping.keys()):
                    print('function '+k+' -> component',mapping[k],' -> node ',r[int(mapping[k])+1])
                    res_file.write('function '+k+' -> node '+str(r[int(mapping[k])+1])+'\t')
                print('======')
                res_file.write('\n')

    return 

def get_routes(solver):
    log('Route')
    if solver.check()!=sat:
        log('No solution!')
        return None
    
    routes = []
    count = 0
    while(solver.check()==sat):
        log('Solution %d:' %(count+1))
        count = count + 1
        m = solver.model()
        paths = []
        cons = [[] for i in range(F)]
        for d in m.decls():
            if m[d]==1:
                print("{}".format(d.name()),end=', ')
                paths.append(d.name())   
                # cons6: no repeat edge
                f = d.name().split('_')[1]
                cons[int(f)].append(d()==0)
        cons = [And(c) for c in cons]
        solver.append(Or(cons))         
        routes.append(check_routes(paths)) # a solution for all the flows
        print('======')
    return routes

def check_routes(paths):
    routes = []
    for f in range(F):
        log('#Flow '+str(f+1)+': ')
        s = S[f]
        d = D[f]
        flow = {}
        route = []
        for u in paths:
            u = u.split('_')[1:]
            i = u[0]
            nodes = u[1:]
            if int(i) == f:
                if nodes[0] in flow:
                    print('Repeated node, wrong route!')
                    return
                else:
                    flow[nodes[0]] = nodes[1]

        # trace the flow
        log(str(s),sep='->')
        route.append(s)
        second = flow[str(s)]
        while second in flow:
            log(second,sep='->')
            route.append(int(second))
            second = flow[second]
        route.append(int(second))
        if second == str(d) and len(route)>=T+2:
            log(str(d))
            print('correct route!')
        elif second != str(d):
            log(second)
            log('###Not reaching destination, wrong route!')
            route = []
        else:
            log(str(d))
            log('###Too short lenghth, wrong route!')
            route = []
        routes.append(route)

    return routes

def log(sen,sep=None):
    if sep:
        print(sen,sep,end='')
        res_file.write(sen+sep)
    else:
        print(sen)
        res_file.write(sen+'\n')

def main():
    times = []
    times.append(time.time())
    
    solver = get_solver()
    times.append(time.time())
    print('adding constraints time:',times[-1]-times[0])

    routes = get_routes(solver)
    mapping = get_mapping(routes)
    
    times.append(time.time())
    print('total time used:',times[-1]-times[0])
    print('======')

if __name__=='__main__':
    res_file = open('RRM_result.txt','w',encoding='utf-8')
    edges,B = load_edges('network-brand.txt')
    cpu = open('CPU.txt','r')
    C = cpu.readlines()
    main()
    res_file.close()