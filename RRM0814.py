######
# 8.13 add bilateral topology
# 8.2 multi flows with multi function chains
# get_route -> every possible routes for each flow
#           length<=L
#           length>=T+1
# get_mapping -> mapping SFC to every possible route (length>=T+1)
# -[x] 只在路径没有成环时加入到不重复edge的约束
# -[√] 实在不行就从有重复边的解里挑几个
# -[√] T = [3,4,5]
######

from z3 import *
import time
import random
import numpy as np

# define global variables
N = 100 # number of nodes
B_sfc = [30,30,30] # service function chian Brandwidth
B_node = 1 # max number of flow on one node
L = 8 # max route Length
T = [3,3,3] # number of functions
F = len(T) # number of flows
S = [50,6,87]
D = [0,2,43]
S = [int(random.random()*N) for i in range(F)]
D = [int(random.random()*N) for i in range(F)]
c = [10,20,20,10,10] # service function CPU requirement
file = 'RRM_result_3_3.txt'

# load two-way topology
def load_edges(file):
    edges = {} 
    B = {}
    topo = [] # topo[i] concludes the nodes connected to node i
    with open(file) as f:
        datas = f.readlines()
  
    for d in datas:
        d = d.split()
        d = [int(x) for x in d]
        i,j,b = d[0],d[1],d[2]
        if i in edges:
            edges[i].append([j,b])
        else:
            edges[i] = [[j,b]]
        if j in edges:
            edges[j].append([i,b])
        else:
            edges[j] = [[i,b]]
        
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
    outs = [E[f][i][j] for j in range(len(E[f][i]))]
    return Sum(outs)

# sum of incoming edges (z3)
def edges_in(E,i,f):
    in_nodes = search_in(i,f)
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
        outs = E[f][i]
        nodes+=outs
    return Sum(nodes)

# find incoming edges to node i
def search_in(i,f):
    nodes = []
    for j in range(N):
        e = edges[j]
        count = 0
        for k in range(len(e)):
            if B_sfc[f]<=search_b([j,e[k]])[0]:
                if e[k]==i:
                    nodes.append([j,count])
                count = count+1
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

def dfs(E,s,d,S=None,route=None,res=None):
    if S is None:
        S=set()
    if route is None:
        route=[]
        res=[]
    route.append(s)
    S.add(s)
    for u in E[s]:
        if (u in S) or (u in route) or (len(route)>L):
            continue
        if ((u==d) and (u not in route)):
            res.append(route+[u])
            break
        # if len(res)>1000:
        #     break
        S.add(u)
        dfs(E,u,d,S,route,res)
        route.pop()
        S.remove(u)

    return res

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
                # constraint brandwidth
                if B_sfc[f]>search_b([i,e])[0]:
                    continue
                tmp.append(Int(name))
                edge = tmp[count]
                cons = Or(edge==1,edge==0)
                constrains.append(cons)
                count = count + 1
            flow.append(tmp)
        E.append(flow)

    # available = [[] for i in range(F)]
    for f in range(F):
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
                # cons: flow constraint
                z = edges_node(E,i)
                cons = z<=B_node
                constrains.append(cons)

        # cons: only 1 route comes out from Source
        x = edges_out(E,S[f],f)
        y = edges_in(E,S[f],f)
        constrains.append(x==1)
        constrains.append(y==0)

        # cons: only 1 route comes inro from Source
        x = edges_out(E,D[f],f)
        y = edges_in(E,D[f],f)
        constrains.append(x==0)
        constrains.append(y==1)

        # cons: length constraint
        ls = [E[f][i][count] for i in range(N) for count in range(len(E[f][i]))]
        length = Sum(ls)
        cons = length<=L
        constrains.append(cons)
        cons = length>=T[f]+1
        constrains.append(cons)

    solver.add(constrains)
    return solver

# map service functions to nodes except S & D
def get_mapping(routes):
    import numpy as np
    routes = np.array(routes) 

    log('Mapping')
    if routes.all()==None:
        log('No routes to mapping!')
        return

    for s in range(len(routes)):
        log('Solution %d' %s)
        for f in range(F):
            # choose viable routes with T function node besides S&D
            route = routes[:,f]
            route = np.unique(route)
            log('##Mapping flow %d :' %(f+1))
            log('#Source node: '+str(S[f]))
            log('#Destination node: '+str(D[f]))
            if len(route) == 0:
                log('##No mapping solution!')
            for r in route:
                if len(r) == 0:
                    continue
                log('##Selected route: '+str(r))
                # B_edges = search_b(r)
                l = len(r)-2
                # generate nodes (components) mapping in z3 variables
                b = [[Int('b_'+str(i)+str(j)) for j in range(T[f])] for i in range(l)]

                solver = Solver()
                for bi in b:
                    for i in bi:
                        solver.append(Or(i==0,i==1))

                # cons1: one function
                for j in range(T[f]):
                    funcs = []
                    for i in range(l):
                        funcs.append(b[i][j])
                    solver.append(Sum(funcs)==1)

                # cons2: service sequence
                for t in range(T[f]):
                    funcs = []
                    for j in range(T[f]):
                        func = []
                        for i in range(t+1):
                            func.append(b[i][j])
                        funcs.append(Sum(func))
                    for k in range(T[f]-1):
                        solver.append(funcs[k]>=funcs[k+1])

                for i in range(l):
                    # cons3: CPU stress
                    resource = [b[i][j]*c[j] for j in range(T[f])]
                    solver.append(Sum(resource)<=C[i])

                    # # cons4: brandwidth
                    # solver.append(B_sfc[f]<=B_edges[i])

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
                        # print('function '+k+' -> component',mapping[k],' -> node ',r[int(mapping[k])+1])
                        res_file.write('function '+k+' -> node '+str(r[int(mapping[k])+1])+'\t')
                    print('======')
                    res_file.write('\n')

    return 

def get_routes(solver):
    log('Finding route')    
    routes = []
    count = 0
    while(solver.check()==sat):
        m = solver.model()
        paths = []
        cons = [[] for i in range(F)]
        for d in m.decls():
            if m[d]==1:
                # print("{}".format(d.name()),end=', ')
                paths.append(d.name())   
                # cons6: no repeat edge
                d_arr = d.name().split('_')
                f= int(d_arr[1])
                cons[f].append(d()==0)
                if int(d_arr[2])==S[f] and int(d_arr[3])==D[f]:
                    solver.append(d()==0)
        
        route, wrong = check_routes(paths) # a solution for all the flows
        if sum(wrong)==0: # check if the solution contains a wrong route
            routes.append(route) 

        for f in range(F):
            cons[f] = Or(cons[f])
            if wrong[f]:
                solver.append(cons[f])            
        solver.append(Or(cons))
        print('======')

    log('Route')
    log('Total solution: %d' %(len(routes)))
    if len(routes)==0:
        log('No solution!')
        return None
        
    for route in routes:
        count = count + 1
        log('Solution %d:' %(count))
        for f in range(F):
            log('#Flow '+str(f+1)+': ')
            s_route = [str(i) for i in route[f]]
            log('->'.join(s_route))
    return routes

def check_routes(paths):
    routes = []
    wrong = [0]*F
    for f in range(F):
        log('#Flow '+str(f+1)+': ')
        s = S[f]
        d = D[f]
        flow = {}
        route = []
        for u in paths:
            us = u.split('_')[1:]
            i = us[0]
            nodes = us[1:]
            if int(i) == f:
                if nodes[0] in flow:
                    print('Repeated node, wrong route!')
                    return [],1
                else:
                    flow[nodes[0]] = nodes[1]

        # trace the flow
        log(str(s),sep='->')
        route.append(s)
        second = flow[str(s)]
        while second in flow:
            log(second,sep='->')
            route.append(int(second))
            key = second
            second = flow[second]
            flow.pop(key)
        route.append(int(second))
        if second == str(d) and len(route)>=T[f]+2:
            log(str(d))
            print('correct route!')
        elif second != str(d):
            log(second)
            log('###Not reaching destination, wrong route!')
            route = []
            wrong[f] = 1
        else:
            log(str(d))
            log('###Too short lenghth, wrong route!')
            route = []
            wrong[f] = 1
        routes.append(route)

    return routes, wrong

def log(sen,sep=None):
    if sep:
        print(sen,sep,end='')
        res_file.write(sen+sep)
    else:
        print(sen)
        res_file.write(sen+'\n')

def main():
    times = []
    times.append(time.process_time())
    
    solver = get_solver()
    routes = get_routes(solver)
    times.append(time.process_time())
    print('Time of finding routes (first mapping):',times[-1]-times[-2])

    mapping = get_mapping(routes)
    times.append(time.process_time())
    print('Time of function mapping (second mapping):',times[-1]-times[-2])
    print('Total time used:',times[-1]-times[0])
    print('======')

if __name__=='__main__':
    res_file = open(file,'w',encoding='utf-8')
    edges,B = load_edges('network-brand.txt')
    cpu = open('CPU.txt','r')
    C = cpu.readlines()
    main()
    res_file.close()