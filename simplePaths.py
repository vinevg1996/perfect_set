#!/usr/bin/python
from combinatorics import Combinatorics

class SimplePaths:
    switchNumber = 0
    hostNumber = 0
    hosts = []
    hosts_to_switch = {}
    simplePathsMatrix = []
    hostSimplePathsMatrix = []

    def __init__(self, switchNumber, hostNumber):
        self.switchNumber = switchNumber
        self.hostNumber = hostNumber
        self.simplePathsMatrix = [[list([]) for x in range(self.switchNumber)] for x in range(self.switchNumber)]
        self.hostSimplePathsMatrix = [[list([]) for x in range(self.hostNumber)] for x in range(self.hostNumber)]

    def SetHosts(self, hosts):
        self.hosts = hosts
        for hostAndSwitch in self.hosts:
            self.hosts_to_switch[hostAndSwitch[0]] = hostAndSwitch[1]

    def GenerateAllSimplePaths(self):
        Comb = Combinatorics()
        for M in range(2, self.switchNumber + 1):
            allPlacements = []
            Comb.GenerationAllPlacements(allPlacements, self.switchNumber - 1, M)
            for placement in allPlacements:
                id_start = placement[0]
                id_fin = placement[len(placement) - 1]
                #print "(",id_start,", ",id_fin,")"
                #print "placement: ",placement
                self.simplePathsMatrix[id_start][id_fin].append(list(placement))
                #print self.simplePathsMatrix[id_start][id_fin]

    def GenerateAllHostSimplePaths(self):
        # hosts = [[h0, s0], [h1, s0], [h2, s1], [h3, s1], [h4, s2]]
        for hostAndSwitch_1 in self.hosts:
            host1_id = hostAndSwitch_1[0]
            switch1_id = hostAndSwitch_1[1]
            it1 = self.hosts_to_switch.get(host1_id)
            for hostAndSwitch_2 in self.hosts:
                host2_id = hostAndSwitch_2[0]
                switch2_id = hostAndSwitch_2[1]
                it2 = self.hosts_to_switch.get(host2_id)
                if (host1_id != host2_id):
                    for simplePaths in self.simplePathsMatrix[switch1_id][switch2_id]:
                        hostSimplePath = list(simplePaths)
                        hostSimplePath.insert(0, int(host1_id))
                        hostSimplePath.append(int(host2_id))
                        self.hostSimplePathsMatrix[host1_id][host2_id].append(list(hostSimplePath))


    def PrintHostsSimplePathsMatrix(self):
        for vec_path in self.hostSimplePathsMatrix:
            for elem in vec_path:
                print elem
                print "________________________"

    def PrintInfoHostsSimplePathsMatrix(self):
        for host1_id in range(0, len(self.hostSimplePathsMatrix)):
            for host2_id in range(0, len(self.hostSimplePathsMatrix)):
                print "(",host1_id, host2_id,")"
                for i in range(0, len(self.hostSimplePathsMatrix[host1_id][host2_id])):
                    print "h",hostSimplePaths[0]
                    hostSimplePaths = self.hostSimplePathsMatrix[host1_id][host2_id][i]
                    for i in range(1, len(hostSimplePaths) - 1):
                        print "s",hostSimplePaths[i]
                    print "h",hostSimplePaths[len(hostSimplePaths) - 1]

    def PrintSimplePathsMatrix(self):
        for vec_path in self.simplePathsMatrix:
            for elem in vec_path:
                print elem
                print "________________________"
