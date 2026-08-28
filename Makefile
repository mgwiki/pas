CFLAGS=-O3 -fPIC # -pg -g -Wcast-align=strict
#MKLIBFLAGS=-custom -ocamloptflags -p
OFLAGS=-O3 # -p
# CFLAGS+= -DHAVE_S2N
# CFLAGS+= -DHAVE_S2N_ALT
OCAMLOPT=ocamlopt
OCAMLC=ocamlc

CINCL=-I secp256k1
OINCL=-I bin # -I +zarith
CDEFS=-DHAVE_CONFIG_H # -DVALGRIND -DVERIFY
CWARN=-Wno-long-long -Wno-overlength-strings -Wno-unused-function
# -pedantic 
CFLAGS+=$(CINCL) $(CDEFS) $(CWARN)
CHIDE=-fvisibility=hidden

S2N=$(wildcard s2n/*.S)
S2NB=$(patsubst s2n/%,bin/%,$(S2N))
S2NO=$(patsubst %.S,%.o,$(S2NB))
BINOBJ=$(addprefix bin/,bebitsstub.o hashbtcstub.o utmstub.o ftm.o bebits.cmx be160.cmi be160.cmx be256.cmi be256.cmx hashbtc.cmx bitlist.cmi bitlist.cmx utm.cmx zarithint.cmi zarithint.cmx utils.cmi utils.cmx ser.cmi ser.cmx hashaux.cmi hashaux.cmx sha256.cmi sha256.cmx hash.cmi hash.cmx logic.cmi logic.cmx mathdata.cmi mathdata.cmx checking.cmi checking.cmx inputdraft.cmi inputdraft.cmx checkdocs.cmx)

checkdocs: Makefile bin $(S2NO) $(BINOBJ)
	$(OCAMLOPT) -I bin -I +unix -I +threads -I +zarith -o checkdocs unix.cmxa threads.cmxa zarith.cmxa $(filter-out %.cmi bin Makefile,$^)

#bin/pgc.cmxa: 
#	ocamlmklib $(MKLIBFLAGS) $(OINCL) -o bin/pgc -cclib -L/usr/lib/x86_64-linux-gnu/ 

clean:
	rm -f bin/* *.o *.cmx *.cmi *.cma *.cmxa *.a *.so *~ *annot gmon.out ocamlprof.dump checkdocs

# GENERAL

bin/%.cmx: src/%.ml Makefile
	$(OCAMLOPT) -I bin -I +zarith -o $@ -c $<

bin/%.cmi: src/%.mli Makefile
	$(OCAMLC) -I bin -I +threads -I +zarith -o $@ -c $<

bin/%.o: src/%.c Makefile
	$(OCAMLC) -ccopt "$(CFLAGS) $(CHIDE)" -c $<
	@mv *.o bin

bin:
	@mkdir -p bin
 
