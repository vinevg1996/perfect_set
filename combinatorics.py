#!/usr/bin/python

class Combinatorics:

    def NextPermutation(self, L): 
        n = len(L)
        i = n - 2
        while i >= 0 and L[i] >= L[i+1]:
            i -= 1
        
        if i == -1:
            return False
    
        j = i + 1
        while j < n and L[j] > L[i]:
            j += 1
        j -= 1

        L[i], L[j] = L[j], L[i]
        
        left = i + 1
        right = n - 1

        while left < right:
            L[left], L[right] = L[right], L[left]
            left += 1
            right -= 1
                
        return True

    def NextSetCombination(self, array, N, M):
        k = M
        for i in range(k - 1, -1, -1):
            if (array[i] < N - k + i + 1):
                array[i] = array[i] + 1
                for j in range(i + 1, k):
                    array[j] = array[j - 1] + 1
                return True
        return False

    def GenerationAllCombinations(self, allCombinations, N, M):
        combination = []
        for i in range(0, M):
            combination.append(i)
        allCombinations.append(list(combination))
        while self.NextSetCombination(combination, N - 1, M):
            allCombinations.append(list(combination))
        return

    def GenerationAllPlacements(self, allPlacements, N, M):
        combination = []
        permutaion = []
        for i in range(0, M):
            combination.append(i)
        permutaion = list(combination)
        allPlacements.append(list(permutaion))
        while self.NextPermutation(permutaion):
            allPlacements.append(list(permutaion))
        while self.NextSetCombination(combination, N, M):
            permutaion = list(combination)
            allPlacements.append(list(permutaion))
            while self.NextPermutation(permutaion):
                allPlacements.append(list(permutaion))
        return
