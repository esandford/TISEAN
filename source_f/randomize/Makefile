# Generated automatically from Makefile.in by configure.
SHELL = /bin/sh

prefix = /Users/Emily
exec_prefix = ${prefix}
BINDIR = ${exec_prefix}/bin

FC = gfortran
FFLAGS = -O
INSTALL = /sw/bin/ginstall -c
LDFLAGS = 

LOADLIBES = ../libtsa.a ../libsla.a

SRC = randomize.f cost/$(COST).o cool/$(COOL).o perm/$(PERM).o
TRG = randomize_$(COST)_$(COOL)_$(PERM)

all install clean missing uninstall:
	-$(MAKE) COST=auto      COOL=exp PERM=random $@-one
	-$(MAKE) COST=autop     COOL=exp PERM=random $@-one
	-$(MAKE) COST=spikeauto COOL=exp PERM=random $@-one
	-$(MAKE) COST=spikespec COOL=exp PERM=event  $@-one
	-$(MAKE) COST=uneven    COOL=exp PERM=random $@-one
# add more similar lines for each module you have written
# for example if you created cost/mycost.f
#	-$(MAKE) COST=mycost  COOL=exp PERM=random $@-one

install-one: $(TRG)
	-$(INSTALL) $(TRG) $(BINDIR)

missing-one:
	-@$(TRG) -h 2>&1 | cat >>  ../../install.log
	-@test -z "`$(TRG) -h 2>&1 | grep Usage`" \
	   && echo $(TRG) "(Wuppertal Fortran)" >>  ../../missing.log; :

uninstall-one:
	-@rm -f $(BINDIR)/$(TRG)

clean-one: 
	@rm -f $(TRG)

all-one: $(TRG)

$(TRG): $(SRC)
	-$(FC) $(FFLAGS) $(SRC) -o $(TRG) $(LOADLIBES) $(LDFLAGS)

cost/$(COST).o: cost/$(COST).f
	$(FC) $(FFLAGS) -c cost/$(COST).f -o cost/$(COST).o

cool/$(COOL).o: cool/$(COOL).f
	$(FC) $(FFLAGS) -c cool/$(COOL).f -o cool/$(COOL).o

perm/$(PERM).o: perm/$(PERM).f
	$(FC) $(FFLAGS) -c perm/$(PERM).f -o perm/$(PERM).o
