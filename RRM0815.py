######
# 8.15 change to node constraint
# 8.13 add bilateral topology
# 8.2 multi flows with multi function chains
# get_route -> every possible routes for each flow
#           length<=L
#           length>=T+1
# get_mapping -> mapping SFC to every possible route (length>=T+1)
# -[√] 改边的变量为节点变量，减少变量个数，加快求解
# -[x] reachability constraint?
######

from z3 import *
import time
import random
import numpy as np

# define global variables
N = 100 # number of nodes
B_sfc = [30,30,30] # service function chian Brandwidth
B_node = 1 # max number of flow on one node
L = 6 # max route Length
T = [3,3,3] # number of functions
F = len(T) # number of flows
S = [50,6,87]
D = [0,2,43]
# S = [int(random.random()*N) for i in range(F)]
# D = [int(random.random()*N) for i in range(F)]
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
def nodes_out(E,i,f):
    outs = [E[f][j] for j in edges[i]]
    return outs

# sum of incoming edges (z3)
def edges_in(E,i,f):
    in_nodes = search_in(i,f)
    if in_nodes:
        ins = [E[f][node] for node in in_nodes]
        y = Sum(ins)
    else:
        y = 0
    return y

# find incoming edges to node i
def search_in(i,f):
    nodes = []
    for j in range(N):
        e = edges[j]
        for k in range(len(e)):
            if e[k]==i:
                nodes.append(j)
    return nodes

# sum of flows coming into a node
def edges_node(E,i):
    nodes = []
    for f in range(F):
        nodes.append(E[f][i])
    return Sum(nodes)

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

# calculate the distance of every reachable node for Ci(src)
# dijkstra算法实现，有向图和路由源点作为函数的输入，最短路径最为输出
def dijkstra(src):
    graph = []
    # 补全有向拓扑图graph[i][j]为i到j的直接距离，不可达为inf，可达为1
    for i in range(len(edges)):
        nodes = edges[i]
        line = [float('inf')]*N
        for n in nodes:
            line[n] = 1
        graph.append(line)
    nodes = [i for i in range(len(graph))]  # 获取图中所有节点
    visited=[]  # 表示已经路由到最短路径的节点集合
    if src in nodes:
        visited.append(src)
        nodes.remove(src)
    else:
        print ('source node out of range!')
        return None
    distance={src:0}  # 记录源节点到各个节点的距离
    for i in nodes:
        distance[i]=graph[src][i]  # 初始化
    # path={src:{src:[]}}  # 记录源节点到每个节点的路径
    k=pre=src
    while nodes:
        mid_distance=float('inf')
        for v in visited:
            for n in nodes:
                new_distance = distance[v]+graph[v][n]
                if new_distance < mid_distance:
                    mid_distance=new_distance
                    graph[src][n]=new_distance  # 进行距离更新
                    k=n
                    pre=v
        distance[k]=mid_distance  # 最短路径
        # path[src][k]=path[src][pre]+[k]
        # 更新两个节点集合
        if k in visited: # 没有新的可达节点
            break
        visited.append(k)
        if k in nodes:
            nodes.remove(k)
    return distance

# generate available route
def get_solver():
    constrains = []
    solver = Solver()
    # generate edges in z3 variables

    E = [] #E:[f_0,f_1...f_F] f_0:[c01,c02,c03...]
    for f in range(F):
        E_f = []
        for i in range(N):
            name = 'c_'+str(f)+'_'+str(i)
            node = Int(name)
            E_f.append(node)
            cons = Or(node==1,node==0)
            constrains.append(cons)
        E.append(E_f)

    # available = [[] for i in range(F)]
    for f in range(F):
        dis = dijkstra(D[f])
        constrains.append(E[f][S[f]] == 1)
        constrains.append(E[f][D[f]] == 1)

        for i in range(N):
            nodes = nodes_out(E,i,f)
            nears = []
            fars = []
            if (i != S[f] and i != D[f]):
                # Rechability constraint
                # for n in nodes:
                #     k = int(n.decl().name().split('_')[1])
                #     if dis[k]<=dis[i]:
                #         nears.append(n)
                #     if dis[k]>=dis[i]:
                #         fars.append(n)
                # if nears != [] and fars != []:
                #     cons = And(Sum(nears)>0,Sum(fars)>0)
                #     constrains.append(Implies(E[f][i]==1, cons))
                # else:
                #     constrains.append(E[f][i]!=1)
                
                # cons: flow constraint
                z = edges_node(E,i)
                cons = z<=B_node
                constrains.append(cons)
                
                # Loop constraint
                constrains.append(Implies(E[f][i]==1,Sum(nodes)==2))
            else: # S&D
                if D[f] in edges[S[f]]:
                    constrains.append(Sum(nodes)==2)
                else:
                    constrains.append(Sum(nodes)==1)

        # cons: length constraint
        length = Sum(E[f])
        cons = length<=L
        constrains.append(cons)
        cons = length>=T[f]+2
        constrains.append(cons)

        solver.add(constrains)

    return solver

# map service functions to nodes except S & D
def get_mapping(routes,num):
    log('Mapping')
    if routes==None:
        log('No routes to mapping!')
        return

    import numpy as np
    routes = np.array(routes) 
    routes = random.sample(list(routes),num)
    print('Selected',len(routes),'solutions.')

    for s in range(len(routes)):
        log('Solution %d' %s)
        for f in range(F):
            # choose viable routes with T function node besides S&D
            route = routes[s][f]        
            log('##Mapping flow %d :' %(f+1))
            log('#Source node: '+str(S[f]))
            log('#Destination node: '+str(D[f]))
            log('##Selected route: '+str(route))
            # B_edges = search_b(r)
            l = len(route)-2
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
                solver.append(Sum(resource)<=E_cpu[i])

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
                    log('function '+k+' -> node '+str(route[int(mapping[k])+1])+'\t')
                log('------')
        log('======')
    return 

def get_routes(solver):
    log('Finding route')    
    routes = []
    count = 0
    while(solver.check()==sat):
        count = count + 1
        m = solver.model()
        path = []
        cons = [[] for i in range(F)]
        for d in m.decls():
            if m[d]==1:
                # print("{}".format(d.name()),end=', ')
                path.append(d.name())   
                # cons6: no repeat edge
                d_arr = d.name().split('_')
                f= int(d_arr[1])
                cons[f].append(d()==0)
        
        route, wrong = check_routes(path) # a solution for all the flows
        if sum(wrong)==0: # check if the solution contains a wrong route
            routes.append(route) 

        for f in range(F):
            cons[f] = Or(cons[f])
            if wrong[f]:
                solver.append(cons[f])            
        solver.append(Or(cons))
        print('======')

    log('Route')
    log('#Total solution: %d' %(len(routes)))
    log('#Wrong solution number: %d' %(count-len(routes)))
    if len(routes)==0:
        log('No solution!')
        return None
        
    for r in range(len(routes)):
        route = routes[r]
        log('Solution %d:' %(r))
        for f in range(F):
            log('#Flow '+str(f+1)+': ')
            s_route = [str(i) for i in route[f]]
            log('->'.join(s_route))
    return routes

def check_routes(path):
    routes = []
    wrong = [0]*F
    for f in range(F):
        # log('#Flow '+str(f+1)+': ')
        s = S[f]
        d = D[f]
        flow = []
        route = []
        for u in path:
            us = u.split('_')[1:]
            i = int(us[0])
            if i == f:
                if us[0] in flow:
                    print('Repeated node, wrong route!')
                    return [],1
                else:
                    flow.append(int(us[1]))

        # trace the flow
        route.append(s)
        second = s
        # log(str(second),sep='->')
        while second in flow:
            flow.pop(flow.index(second))
            for j in edges[second]:
                if j in flow:
                    second = j
                    # log(str(second),sep='->')
                    route.append(int(second))   
        if second == d and len(route)>=T[f]+2:
            # log('True')
            print('correct route!')
        elif second != d:
            log(str(second))
            log('###Not reaching destination, wrong route!')
            route = []
            wrong[f] = 1
        else:
            log('Flow: '+str(f))
            log('#loop: '+','.join([str(fl) for fl in flow]))
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
    log('#Length of function chain: '+str(T[0]))
    log('#Number of flows: '+str(F))

    times = []
    times.append(time.process_time())
    
    solver = get_solver()
    routes = get_routes(solver)
    times.append(time.process_time())
    log('Time of finding routes (first mapping):'+str(times[-1]-times[-2]))

    mapping = get_mapping(routes,5)
    times.append(time.process_time())
    log('Time of function mapping (second mapping):'+str(times[-1]-times[-2]))
    log('Total time used:'+str(times[-1]-times[0]))
    print('======')

if __name__=='__main__':
    res_file = open(file,'w',encoding='utf-8')
    edges,B = load_edges('network-brand.txt')
    cpu = open('CPU.txt','r')
    E_cpu = cpu.readlines()
    main()
    res_file.close()