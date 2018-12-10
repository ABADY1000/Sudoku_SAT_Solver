from pprint import pprint # pprint() method print matrices in well-looking form
import pycosat # SAT Solver, used to find answers
from math import sqrt

# The matrices to choose from, Assign the wanted matrix to variable 'game' in __main__ method...
#region Matrices

hard = [[0, 2, 0, 0, 0, 0, 0, 3, 0],
        [0, 0, 0, 6, 0, 1, 0, 0, 0],
        [0, 6, 8, 2, 0, 0, 0, 0, 5],
        [0, 0, 9, 0, 0, 8, 3, 0, 0],
        [0, 4, 6, 0, 0, 0, 7, 5, 0],
        [0, 0, 1, 3, 0, 0, 4, 0, 0],
        [9, 0, 0, 0, 0, 7, 5, 1, 0],
        [0, 0, 0, 1, 0, 4, 0, 0, 0],
        [0, 1, 0, 0, 0, 0, 0, 9, 0]]

quad = [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

norm = [[2, 3, 0, 1],
        [1, 0, 3, 2],
        [0, 1, 2, 3],
        [3, 2, 1, 0]]

#endregion

n = 2           # These assignments are just for initialization, it will be changed later in __main__
__n2__ = n ** 2 # The size of the game (this method used since Sudoku (n^2 * n^2) )

# This method is made in porous of printing matrices (the output is not neat up till now)
def printer(mat):
    for line in mat:
        for ele in line:
            print(" {:2d} |".format(ele), end="")
        print(end="\n")


# Variables maker
def p(i, j, d):
    """ This method gives special code for every cell with every possible value """
    if i > __n2__ or j > __n2__ or d > __n2__:
        raise ValueError(f"Rows, Columns and Values, all should be less than __n2__={__n2__}")
    return (i - 1) * __n2__ ** 2 + (j - 1) * __n2__ + d


def generat_clauses(matrix):
    """ Generates the clauses to be used in the SAT_Solver(PicoSAT) """
    clauses = [] # Resulted clauses are going to add here

    def general_clauses_maker():
        """ This inner method will generate general clauses which will be applied for every Sudoku game"""
        # Generating (AtLeastOne) for cells clauses:
        for i in range(1, __n2__+1):
            for j in range(1, __n2__+1):
                clauses.append([p(i, j, d) for d in range(1, __n2__+1)])
                # Generating (AtMostOne) for cells clauses
                for d in range(1, __n2__):
                    for d2 in range(d+1, __n2__+1):
                        clauses.append([-p(i, j, d), -p(i, j, d2)])

        # Generating (AtLeastOne) for rows clauses:
        for i in range(1, __n2__ + 1):
            for d in range(1, __n2__ + 1):
                clauses.append([p(i, j, d) for j in range(1, __n2__ + 1)])
                # Generating (AtMostOne) for rows clauses
                for j in range(1, __n2__):
                    for j2 in range(j + 1, __n2__ + 1):
                        clauses.append([-p(i, j, d), -p(i, j2, d)])

        # Generating (AtLeastOne) for columns clauses:
        for j in range(1, __n2__ + 1):
            for d in range(1, __n2__ + 1):
                clauses.append([p(i, j, d) for i in range(1, __n2__ + 1)])
                # Generating (AtMostOne) for columns clauses
                for i in range(1, __n2__):
                    for i2 in range(i + 1, __n2__ + 1):
                        clauses.append([-p(i, j, d), -p(i2, j, d)])

        # Generating (AtLeastOne) for block clauses:
        for si in range(1, __n2__, n):
            for sj in range(1, __n2__, n):
                for d in range(1, __n2__+1):
                    line1 = []
                    for i in range(si, si+n):
                        for j in range(sj, sj+n):
                            line1.append(p(i,j,d))
                            line2 = []
                            # Generating (AtMostOne) for block clauses:
                            for ii in range(si, si + n):
                                for jj in range(sj, sj + n):
                                    if ii == i and jj ==j:
                                        continue
                                    clauses.append([-p(i,j,d), -p(ii,jj,d)])
                    clauses.append(line1)

    def private_clauses():
        """ Simple method that generates clauses that are specific for only one Sudoku game """
        for row in range(1, __n2__+1):
            for col in range(1, __n2__+1):
                d = matrix[row-1][col-1]
                if d:
                    clauses.append([p(row, col, d)])

    # Run the methods
    general_clauses_maker()
    private_clauses()

    return clauses


def solution_finder(matrix, clauses):
    """  This method is used to find the answers for a solution from SAT_Solver """
    for row in range(1, __n2__+1):
        for col in range(1, __n2__+1):
            if not matrix[row - 1][col - 1]:
                for v in range(1, __n2__+1):
                    if p(row, col, v) in clauses:
                        matrix[row - 1][col - 1] = v
                        break
    return matrix


if __name__ == '__main__':

    # Assign to 'game' the matrix to solve
    game = norm
    pprint(game) # print the problem before solve it

    # find 'n' and '__n2__' values based on the chosen matrix
    n = int(sqrt(len(game[0])))
    __n2__ = n ** 2

    # Generating the clauses
    cls = generat_clauses(game)

    # Find all possible solutions
    sols = list(pycosat.itersolve(cls))

    print("The number of solutions are: {}".format(len(sols)))
    # Find the solution for the first possible solution if it exist
    if len(sols) > 0:
        solved_sudoku = solution_finder(game, sols[0])
        pprint(solved_sudoku)
    else:
        print("There is no solutions")

