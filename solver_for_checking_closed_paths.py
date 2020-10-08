#!/usr/bin/python
from z3 import *
from combinatorics import Combinatorics
from simplePaths import SimplePaths

def convert_decimal_to_binary(dec, base):
    string = "{0:{fill" + "}" + str(base) + "b}"
    res_str = string.format(dec, fill='0')
    res_dig = [int(sym) for sym in res_str]
    return res_dig

def convert_binary_to_decimal(self, binary_list, base):
    dig = 0
    for i in range(0, base):
        dig = dig + binary_list[i] * (2 ** (base - i - 1))
    return dig

class SolverForClosedPaths:

    def __init__(self, switch_number, host_number, hosts):
        self.switch_number = switch_number
        self.host_number = host_number
        self.hosts = hosts
        self.simplePaths = SimplePaths(self.switch_number, self.host_number)
        self.simplePaths.GenerateAllSimplePaths()
        self.simplePaths.SetHosts(self.hosts)
        self.simplePaths.GenerateAllHostSimplePaths()
        self.hostSimplePaths = self.simplePaths.hostSimplePathsMatrix
        return

    def create_solver_env(self, curr_host_maska, curr_host_pairs):
        solver = Solver()
        Paths = [[Array('paths_%d_%d' % (i, j), IntSort(), ArraySort(IntSort(), IntSort())) 
                    for j in range(0, self.host_number)] for i in range(0, self.host_number)]
        ids = [[Int('ids_%d_%d' % (i, j)) for j in range(0, self.host_number) ] 
                    for i in range(0, self.host_number) ]
        x_var = [[Int('x_var_%d_%d' % (i, j)) for j in range(0, self.host_number) ] 
                    for i in range(0, self.host_number) ]
        Hosts = [[Int('host_%d_%d' % (i, j)) for j in range(0, self.host_number) ] 
                    for i in range(0, self.host_number) ]
        for i in range(0, self.host_number):
            for j in range(0, self.host_number):
                if (curr_host_maska[i][j] == 1):
                    for k in range(0, len(self.hostSimplePaths[i][j])):
                        solver.add(Paths[i][j][k][0] == len(self.hostSimplePaths[i][j][k]))
                        for l in range(0, len(self.hostSimplePaths[i][j][k])):
                            solver.add(Paths[i][j][k][l + 1] == self.hostSimplePaths[i][j][k][l])
        for i in range(0, self.host_number):
            for j in range(0, self.host_number):
                if (curr_host_maska[i][j] == 1):
                    solver.add(ids[i][j] >= 0)
                    solver.add(ids[i][j] < len(self.hostSimplePaths[i][j]))
                    solver.add(Hosts[i][j] == 1)
                else:
                    solver.add(Hosts[i][j] == 0)
        i = 0
        while i < len(curr_host_pairs):
            row_1 = curr_host_pairs[i][0]
            col_1 = curr_host_pairs[i][1]
            path_i = Paths[row_1][col_1][ids[row_1][col_1]]
            len_x = path_i[0]
            j = i + 1
            while j < len(curr_host_pairs):
                row_2 = curr_host_pairs[j][0]
                col_2 = curr_host_pairs[j][1]
                path_j = Paths[row_2][col_2][ids[row_2][col_2]]
                len_y = path_j[0]
                x = x_var[row_1][col_1]
                y = x_var[row_2][col_2]
                w0 = And(Or(path_i[1] != path_j[1], 
                            path_i[2] != path_j[2]), 
                         Or(path_i[len_x - 1] != path_j[len_y - 1],
                            path_i[len_x] != path_j[len_y]))
                w1 = Exists([x, y], And(
                            And(x >= 2, x < len_x - 1, y >= 2, y < len_y - 1),
                            And((path_i[x] == path_j[y]), (path_i[x + 1] == path_j[y + 1]))
                            ))
                w_01 = And(w0, w1)
                G = And(Hosts[row_1][col_2] == 1, Hosts[row_2][col_1] == 1)
                F = Implies(w_01, G)
                solver.add(F)
                j = j + 1
            i = i + 1
        solver_check = solver.check()
        print solver_check
        if (solver_check == z3.sat):
            return "sat"
        elif (solver_check == z3.unsat):
            return "unsat"
        return

    def is_covered(self, path1, path2):
        bool_matrix = [[False for y in range(0, self.switch_number)] for x in range(0, switch_number)]
        for i in range(0, len(path1) - 1):
            bool_matrix[path1[i]][path1[i + 1]] = True
        for i in range(0, len(path2) - 1):
            if (bool_matrix[path2[i]][path2[i + 1]] == True):
                return True
        return False

    def is_closed_set(self, vec_ids, curr_host_maska, curr_host_pairs):
        i = 0
        flag = True
        while (i < len(curr_host_pairs)) and (flag):
            row1 = curr_host_pairs[i][0]
            col1 = curr_host_pairs[i][1]
            value1 = vec_ids[i]
            path1 = self.hostSimplePaths[row1][col1][value1]
            j = i + 1
            while (j < len(curr_host_pairs)) and (flag):
                row2 = curr_host_pairs[j][0]
                col2 = curr_host_pairs[j][1]
                value2 = vec_ids[j]
                path2 = self.hostSimplePaths[row2][col2][value2]
                if (path1[0:2] != path2[0:2]) and (path1[len(path1) - 2 :] != path2[len(path2) - 2 :]):
                    if (self.is_covered(path1[1 : len(path1) - 1], path2[1 : len(path2) - 1])):
                        if ((curr_host_maska[row1][col2] != 1) or (curr_host_maska[row2][col1] != 1)):
                            #print "path1: ", path1
                            #print "path2: ", path2
                            flag = False
                j = j + 1
            i = i + 1
        return flag

    def verify_complete_set(self, curr_host_maska, curr_host_pairs):
        size = len(curr_host_pairs)
        for i in range(0, 2 ** size):
            vec_ids = convert_decimal_to_binary(i, size)
            if (self.is_closed_set(vec_ids, curr_host_maska, curr_host_pairs)):
                print "complete_set:"
                j = 0
                while j < len(curr_host_pairs):
                    row = curr_host_pairs[j][0]
                    col = curr_host_pairs[j][1]
                    value = vec_ids[j]
                    path = self.hostSimplePaths[row][col][value]
                    print "path = ", path
                    j = j + 1
                print "curr_host_maska:"
                for curr_list in curr_host_maska:
                    print(curr_list)
                print "curr_host_pairs = ", curr_host_pairs
                return True
        return False

    def check_complete_set_with_program(self):
        in_host_maska = [[0 for j in range(0, self.host_number) ]
                            for i in range(0, self.host_number) ]
        Comb = Combinatorics()
        allHostPairs = []
        Comb.GenerationAllPlacements(allHostPairs, self.host_number - 1, 2)
        allDiffHostPairs = []
        for host_pair in allHostPairs:
            host1 = host_pair[0]
            host2 = host_pair[1]
            in_host_maska[host1][host1] = 1
            for host_and_switch1 in self.hosts:
                if (host_and_switch1[0] == host1):
                    switch1 = host_and_switch1[1]
                if (host_and_switch1[0] == host2):
                    switch2 = host_and_switch1[1]
            if (switch1 != switch2):
                allDiffHostPairs.append(list(host_pair))
            else:
                in_host_maska[host1][host2] = 1
        print "allDiffHostPairs: ", allDiffHostPairs
        diffPaths = len(allDiffHostPairs)
        print "diffPaths = ", diffPaths
        print "in_host_maska: "
        for curr_list in in_host_maska:
            print(curr_list)
        #for level in range(9, diffPaths + 1):
        for level in range(9, 10):
            print "level = ", level
            idHostConnections = []
            Comb.GenerationAllCombinations(idHostConnections, diffPaths, level)
            for id_hosts in idHostConnections:
                curr_host_maska = [[0 for j in range(0, self.host_number) ]
                                    for i in range(0, self.host_number) ]
                for row in range(0, self.host_number):
                        for col in range(0, self.host_number):
                            if (in_host_maska[row][col] == 1):
                                curr_host_maska[row][col] = 1
                curr_host_pairs = list()
                for id_pair in id_hosts:
                    curr_host_pairs.append(list(allDiffHostPairs[id_pair]))
                    host1 = allDiffHostPairs[id_pair][0]
                    host2 = allDiffHostPairs[id_pair][1]
                    curr_host_maska[host1][host2] = 1
                flag = self.verify_complete_set(curr_host_maska, curr_host_pairs)
                if (flag == True):
                    print "id_hosts = ", id_hosts
                    break
            print "all hosts are closed"
        return

    def check_complete_set(self):
        in_host_maska = [[0 for j in range(0, self.host_number) ]
                            for i in range(0, self.host_number) ]
        Comb = Combinatorics()
        allHostPairs = []
        Comb.GenerationAllPlacements(allHostPairs, self.host_number - 1, 2)
        allDiffHostPairs = []
        for host_pair in allHostPairs:
            host1 = host_pair[0]
            host2 = host_pair[1]
            in_host_maska[host1][host1] = 1
            for host_and_switch1 in self.hosts:
                if (host_and_switch1[0] == host1):
                    switch1 = host_and_switch1[1]
                if (host_and_switch1[0] == host2):
                    switch2 = host_and_switch1[1]
            if (switch1 != switch2):
                allDiffHostPairs.append(list(host_pair))
            else:
                in_host_maska[host1][host2] = 1
        print "allDiffHostPairs: ", allDiffHostPairs
        diffPaths = len(allDiffHostPairs)
        print "diffPaths = ", diffPaths
        print "in_host_maska: "
        for curr_list in in_host_maska:
            print(curr_list)
        for level in range(8, diffPaths + 1):
            print "level = ", level
            idHostConnections = []
            Comb.GenerationAllCombinations(idHostConnections, diffPaths, level)
            for id_hosts in idHostConnections:
                curr_host_maska = [[0 for j in range(0, self.host_number) ]
                                    for i in range(0, self.host_number) ]
                for row in range(0, self.host_number):
                        for col in range(0, self.host_number):
                            if (in_host_maska[row][col] == 1):
                                curr_host_maska[row][col] = 1
                curr_host_pairs = list()
                for id_pair in id_hosts:
                    curr_host_pairs.append(list(allDiffHostPairs[id_pair]))
                    host1 = allDiffHostPairs[id_pair][0]
                    host2 = allDiffHostPairs[id_pair][1]
                    curr_host_maska[host1][host2] = 1
                flag = self.create_solver_env(curr_host_maska, curr_host_pairs)
                if (flag == "unsat"):
                    print "there exists nonclosed hosts"
                    print "in_host_maska: "
                    for curr_list in in_host_maska:
                        print curr_list
                    print "curr_host_pairs: ", curr_host_pairs
                    return
            print "all hosts are closed"
        return

    def debug_add_hosts(self, solver, Hosts):
        solver.add(Hosts[0][0] == 0)
        solver.add(Hosts[0][1] == 0)
        solver.add(Hosts[0][2] == 0)
        solver.add(Hosts[0][3] == 0)
        solver.add(Hosts[0][4] == 0)
        solver.add(Hosts[1][0] == 0)
        solver.add(Hosts[1][1] == 0)
        solver.add(Hosts[1][2] == 0)
        solver.add(Hosts[1][3] == 0)
        solver.add(Hosts[1][4] == 0)
        solver.add(Hosts[2][0] == 0)
        solver.add(Hosts[2][1] == 1)
        solver.add(Hosts[2][2] == 0)
        solver.add(Hosts[2][3] == 0)
        solver.add(Hosts[2][4] == 0)
        solver.add(Hosts[3][0] == 1)
        solver.add(Hosts[3][1] == 0)
        solver.add(Hosts[3][2] == 0)
        solver.add(Hosts[3][3] == 0)
        solver.add(Hosts[3][4] == 0)
        solver.add(Hosts[4][0] == 0)
        solver.add(Hosts[4][1] == 0)
        solver.add(Hosts[4][2] == 0)
        solver.add(Hosts[4][3] == 0)
        solver.add(Hosts[4][4] == 0)
        return

    def verify_complete_set_from_ids(self, model_ids, curr_host_maska, curr_host_pairs):
        i = 0
        flag = True
        while (i < len(curr_host_pairs)) and (flag):
            row1 = curr_host_pairs[i][0]
            col1 = curr_host_pairs[i][1]
            value1 = int(model_ids[row1][col1])
            path1 = self.hostSimplePaths[row1][col1][value1]
            j = i + 1
            while (j < len(curr_host_pairs)) and (flag):
                row2 = curr_host_pairs[j][0]
                col2 = curr_host_pairs[j][1]
                value2 = int(model_ids[row2][col2])
                path2 = self.hostSimplePaths[row2][col2][value2]
                if (path1[0:2] != path2[0:2]) and (path1[len(path1) - 2 :] != path2[len(path2) - 2 :]):
                    if (self.is_covered(path1[1 : len(path1) - 1], path2[1 : len(path2) - 1])):
                        if ((curr_host_maska[row1][col2] != 1) or (curr_host_maska[row2][col1] != 1)):
                            #print "path1: ", path1
                            #print "path2: ", path2
                            flag = False
                j = j + 1
            i = i + 1
        return flag

    def debug_check_complete_set(self, curr_host_maska, curr_host_pairs, host_conn_maska):
        solver = Solver()
        Paths = [[Array('paths_%d_%d' % (i, j), IntSort(), ArraySort(IntSort(), IntSort())) 
                    for j in range(0, self.host_number)] for i in range(0, self.host_number)]
        ids = [[Int('ids_%d_%d' % (i, j)) for j in range(0, self.host_number) ] 
                    for i in range(0, self.host_number) ]
        x_var = [[Int('x_var_%d_%d' % (i, j)) for j in range(0, self.host_number) ] 
                    for i in range(0, self.host_number) ]
        Hosts = [[Int('host_%d_%d' % (i, j)) for j in range(0, self.host_number) ] 
                    for i in range(0, self.host_number) ]
        for i in range(0, self.host_number):
            for j in range(0, self.host_number):
                if (host_conn_maska[i][j] == 1):
                    for k in range(0, len(self.hostSimplePaths[i][j])):
                        solver.add(Paths[i][j][k][0] == len(self.hostSimplePaths[i][j][k]))
                        for l in range(0, len(self.hostSimplePaths[i][j][k])):
                            solver.add(Paths[i][j][k][l + 1] == self.hostSimplePaths[i][j][k][l])
        for i in range(0, self.host_number):
            for j in range(0, self.host_number):
                if (curr_host_maska[i][j] == 1):
                    solver.add(Hosts[i][j] == 1)
                else:
                    solver.add(Hosts[i][j] == 0)
        for i in range(0, self.host_number):
            for j in range(0, self.host_number):
                if (host_conn_maska[i][j] == 1):
                    solver.add(ids[i][j] >= 0)
                    solver.add(ids[i][j] < 2)
        i = 0
        while i < len(curr_host_pairs):
            row_1 = curr_host_pairs[i][0]
            col_1 = curr_host_pairs[i][1]
            path_i = Paths[row_1][col_1][ids[row_1][col_1]]
            len_x = path_i[0]
            j = i + 1
            while j < len(curr_host_pairs):
                row_2 = curr_host_pairs[j][0]
                col_2 = curr_host_pairs[j][1]
                path_j = Paths[row_2][col_2][ids[row_2][col_2]]
                len_y = path_j[0]
                x = x_var[row_1][col_1]
                y = x_var[row_2][col_2]
                w0 = And(Or(path_i[1] != path_j[1], 
                            path_i[2] != path_j[2]), 
                         Or(path_i[len_x - 1] != path_j[len_y - 1],
                            path_i[len_x] != path_j[len_y]))
                w1 = Exists([x, y], And(
                            And(x >= 2, x < len_x - 1, y >= 2, y < len_y - 1),
                            And((path_i[x] == path_j[y]), (path_i[x + 1] == path_j[y + 1]))
                            ))
                w_01 = And(w0, w1)
                G = And(Hosts[row_1][col_2] == 1, Hosts[row_2][col_1] == 1)
                F = Implies(w_01, G)
                solver.add(F)
                j = j + 1
            i = i + 1
        solver_check = solver.check()
        print solver_check
        if (solver_check == z3.sat):
            model_ids = [[str(-1) for j in range(0, self.host_number) ]
                            for i in range(0, self.host_number) ]
            solver_model = solver.model()
            for i in range(0, self.host_number):
                for j in range(0, self.host_number):
                    if (host_conn_maska[i][j] == 1):
                        model_ids[i][j] = str(solver_model[ids[i][j]])
            print "model_ids:"
            for curr_list in model_ids:
                print curr_list
            print self.verify_complete_set_from_ids(model_ids, curr_host_maska, curr_host_pairs)
        return
        

print "_______________________"
print "_______________________"
print "_______________________"
print "z3 starts working"
print "_______________________"

'''
hosts = [[0, 0], [1, 0], [2, 1], [3, 1], [4, 2], [5, 3]]
switch_number = 4
host_number = 6

host_maska = [[0, 0, 1, 1, 1, 1],
              [0, 0, 1, 1, 1, 1],
              [1, 1, 0, 0, 1, 1],
              [1, 1, 0, 0, 1, 1],
              [1, 1, 1, 1, 0, 1],
              [1, 1, 1, 1, 1, 0]]
'''

hosts = [[0, 0], [1, 0], [2, 1], [3, 1], [4, 2]]
switch_number = 3
host_number = 5

curr_host_pairs = [[0, 2], [2, 0], [0, 3], [3, 0], [0, 4], [4, 0], [1, 2], [2, 1], [1, 3]]
curr_host_maska = [[1, 1, 1, 1, 1],
                   [1, 1, 1, 1, 0],
                   [1, 1, 1, 1, 0],
                   [1, 0, 1, 1, 0],
                   [1, 0, 0, 0, 1]]
host_conn_maska = [[0, 0, 1, 1, 1],
              [0, 0, 1, 1, 0],
              [1, 1, 0, 0, 0],
              [1, 0, 0, 0, 0],
              [1, 0, 0, 0, 0]]

solverForPaths = SolverForClosedPaths(switch_number, host_number, hosts)
#solverForPaths.check_complete_set()
#solverForPaths.check_complete_set_with_program()

solverForPaths.debug_check_complete_set(curr_host_maska, curr_host_pairs, host_conn_maska)

#solverForPaths.fill_Paths_and_ids()
#solverForPaths.check_complete_set()