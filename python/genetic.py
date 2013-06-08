# simple genetic algorithm library
import UserList
from whrandom import randint, seed # from NumPy

def randstring(maxlen=200):
    thelist = [randint(ord(" "), ord("z")+1) for x in range(randint(1, maxlen))]
    return "".join([chr(c) for c in thelist])

class IndexLoop:
    def __init__ (self, list):
        self.list = list
    def __getitem__ (self, index):
        return index, self.list [index]


class Specimen:
    def __init__(self, genes=None):
        if genes:
            self.genes = genes
        else:
            self.genes = randstring()
        self.score = self.fitness()
        self.age = 0

    def __hash__(self):
        # this just doesn't seem to work... :/
        return hash(self.genes)

    def segment(self):
        """
        Break my genes into chunks, randomly
        """
        res = []
        idx = 0
        while idx < len(self.genes):
            size = randint(1,4) # small chunks seem to work better
            chunk = self.genes[idx:idx+size]
            res.append(chunk)
            idx += size
        return res
        
    def mate(self, other):
        """
        Let's get it ON! Return our love child. :)
        """
        # map(None, a,b) is like zip(a,b) but allows padding...
        # @TODO: genes @ front are more likely to propagate. fix this!
        sequence = map(None, self.segment(), other.segment())
        newgenes = []
        for pair in sequence:
            gene = pair[randint(0,1)] # either maddy or dommy's gene
            if gene:
                newgenes.append(gene)
        return self.__class__("".join(newgenes))

    def mutate(self):
        """
        Return a mutated clone of myself.
        """
        newgenes = ""
        for gene in self.genes:
            switch = randint(0, 10)
            if switch == 0:
                # randomly replace a gene
                newgenes += randstring(1)
            elif switch == 1:
                pass # delete a gene
            elif switch == 2: # insert a random gene
                newgenes += randstring(1) + gene
            else:
                newgenes += gene
        return self.__class__(newgenes)

    def fitness(self):
        raise NotImplementedError, "score() is your job."
            

class Population(UserList.UserList):
    __super = UserList.UserList

    def __init__(self, Species, size):
        """
        Create a random population of specimen.
        """
        self.log("initializing...")
        self.__super.__init__(self)
        self.size = size
        self.Species = Species
        for loop in range(self.size):
            self.data.append(self.Species())
        self.ranked = 0
        self.generation = 0

    def log(self, msg):
        #print msg
        pass
    

    def rank(self):
        """
        sort so that highest score becomes self[0]
        """
        self.log("ranking....")
        # we sort by both rank and genes so that we can kill off
        # duplicates...
        self.data.sort(lambda a, b: - (cmp(a.score, b.score)))
        self.ranked = 1

    def slaughter(self):
        """
        Kill off the weakest 50%
        """
        self.log("slaughtering...")
        assert self.ranked, "must be ranked to kill weaklings"
        self.data = self.data[:- len(self.data)/2]

    def breed(self):
        """
        Weakest remaining guy mates with one tenth the population,
        next fittest with a tenth of what's left, and so
        on, until we run out of mates. Also: weakest guy
        gets the strongest harem.
        """
        self.log("breeding...")
        self.ranked = 0

        start = 0 # start of the harem....
        pop = self.data
        stud = 0
        breedercount = len(pop)
        childcount = 0
        while 1:
            tenth = (9+breedercount-start)/10
            if tenth == 0:
                break
            harem = pop[start:start+tenth]
            start = start+tenth
            for wife in harem:  # heh... how sexist... :)
                pop.append(pop[stud].mate(wife))
                pop.append(pop[stud].mate(wife))
                pop.append(pop[-1-stud].mate(wife)) #anti-stud
            stud += 1 # all done... let the next one have some fun.
        self.show()
        

    def mutate(self):
        """
        Fill out the population with mutants.
        This also removes any duplicates....
        """
        self.log("mutating....")

        # first make a dictionary... dictionary keys
        # are always unique, so this strips out duplicates.
        unique = {}
        for item in self.data:
            # __hash__ doesn't seem to work, so we use .genes :/
            unique[item.genes] = item

        # now add mutants until we reach the size we want.
        x = 0
        mutators = self.size / 20 # only mutate top 5%
        while len(unique) < self.size:
            mutant = self.data[x % mutators].mutate()
            unique[mutant.genes] = mutant
            x += 1

        # now turn the dict back to a list.
        self.data = unique.values()
        self.ranked = 0

    def step(self):
        self.rank()
        self.show()
        self.slaughter() # kill the bottom 
        self.breed()     # replace middle section via sexual reproduction
        self.mutate()    # replace rest with mutant clones
        self.generation += 1

    def show(self):
        self.log(("-- generation %i" % self.generation) + "-" * 30)
##         for item in self.data:
##             print item.score,
##         print
##         for x in range(5):
##             # best and worst 5
##             print x, self[x].genes, "          " , self[-x-1].genes
##         #print "%02s:" % self.generation, self[0].genes



class StudPopulation(Population):
    def slaughter(self):
        # don't kill anyone
        pass
    def breed(self):
        # breed bottom 80% with top 20%
        for x in range(self.size / 5, 4 * self.size / 5):
            self[x] = self[x].mate(self[randint(0, self.size/5)])
    def mutate(self):
        # mutate lower 10% at random
        self.rank() # re-rank after breeding
        for x in range(9 * self.size / 10, self.size):
            self[x] = self[x].mutate()
        

        
if __name__=="__main__":

    # demo code...
    import math
    
    def proximity(a, b):
        """
        It's the pythagorean theorem! Yay!
        """
        res = 0

        for pair in map(None, a, b):
            x,y = pair
            res += pow(ord(x or "\0")-ord(y or "\0"), 2)
        # make it negative so closer is better:
        return - math.sqrt(res)

    def diffchars(a, b):
        res = 0
        for (x,y) in map(None, a, b):
            if x!=y:
                res -= 1
        return res

    TARGET = "Hello, World!" # I am a genetic algorithm!"

    class Hello(Specimen):
        def fitness(self):
            # the lower the stringdist, the better
            #return - stringdist(self.genes, "Hello, World!")
            target = TARGET
            if len(self.genes) > len(target):
                self.genes = self.genes[:len(target)]
            #return proximity(self.genes, target)
            return diffchars(self.genes, target)


    Solved = "XX SOLVED XX"
    try:
        pops = [StudPopulation(Hello, 1000),#0
                StudPopulation(Hello, 500),#1
                StudPopulation(Hello, 500),#2
                StudPopulation(Hello, 500),#3
                StudPopulation(Hello, 50),#4
                StudPopulation(Hello, 500),#5
##                 Population(Hello, 50),#1
##                 Population(Hello, 50),  #2
##                 Population(Hello, 50),  #3
##                 Population(Hello, 50),  #4
##                 Population(Hello, 50), #5
                ]
        for loop in range(0,400):
            for x, pop in IndexLoop(pops):
                pop.rank()
                print "pop %i, gen %2s (score: %0.2f): %s" \
                      % (x, pop.generation, pop[0].score, pop[0].genes)
                if pop[0].score == 0:
                    raise Solved
                pop.step()
            pops[-1].step() # twice as fast...
            print
            if not loop % 5:
                # cross polination....
                for pop in pops: pop.rank()
                for x in range(len(pops)):
                    pops[x][25] = pops[(x+1) % len(pops)][5].mutate()
            if not loop % 20:
                # REALLY spice things up..
                for x in range(0,50):
                    pops[2][x] = pops[1][x].mate(pops[5][x])
    except Solved:
        print "SOLVED!"
