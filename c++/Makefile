CUDD=~/ver/cudd/cudd-2.5.1
CUDDLS=$(CUDD)/obj/libobj.a  \
       $(CUDD)/cudd/libcudd.a \
       $(CUDD)/mtr/libmtr.a \
       $(CUDD)/util/libutil.a \
       $(CUDD)/st/libst.a \
       $(CUDD)/epd/libepd.a

shacudd-run: shacudd
	./shacudd

shacudd: shacudd.o
	clang++ -g -o shacudd shacudd.o $(CUDDLS)

shacudd.o: shacudd.cc
	clang++ -g -c shacudd.cc -I $(CUDD)/include/

