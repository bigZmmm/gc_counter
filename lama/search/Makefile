HEADERS = heuristic.h ff_heuristic.h wa_star_search.h \
	  domain_transition_graph.h globals.h \
          operator.h state.h successor_generator.h \
	  best_first_search.h axioms.h \
	  search_engine.h open_list.h closed_list.h \
	  landmarks_graph.h \
	  landmarks_graph_rpg_sasp.h \
	  landmarks_count_heuristic.h \
	  counter.h \
	  z3_counter.h \

SOURCES = planner.cc $(HEADERS:%.h=%.cc)
OBJECTS = $(SOURCES:%.cc=%.o)
PROFILE_OBJECTS = $(SOURCES:%.cc=%.profile.o)
RELEASE_OBJECTS = $(SOURCES:%.cc=%.release.o)

CC = g++
DEPEND = g++ -MM
CCOPT =      -Wall -W -Wno-sign-compare  -pedantic  -O3 -Wno-deprecated 
RELEASEOPT = -Wall -W -Wno-sign-compare  -pedantic  -DNDEBUG -O3 -m64 -Wno-deprecated 
LINKOPT = -lz3

## debug, don't optimize
CCOPT += -g
LINKOPT += -g

## debug, optimize
# CCOPT += -O3 -g
# LINKOPT += -g

## no debug, optimize a lot
#CCOPT += -O3 -DNDEBUG -march=athlon-xp

PROFOPT = -pg -O2 -DNDEBUG

PROFILE_ARGS = fFxXo fF fFxX fFxXD xX
PROFILE_TASK = driverlog/pfile20

PROFILES = $(PROFILE_ARGS:%=PROFILE-%)

# PROFLINKOPT = -lc_p

vpath %.o obj

search: $(OBJECTS)
	$(CC) $(LINKOPT) $(OBJECTS:%=obj/%) -o search -lz3

profile-search: $(PROFILE_OBJECTS)
	$(CC) $(LINKOPT) $(PROFLINKOPT) $(PROFOPT) $(PROFILE_OBJECTS:%=obj/%) \
          -o profile-search -lz3

release: release-search 

release-search: $(RELEASE_OBJECTS)
	$(CC) $(RELEASEOPT) $(RELEASE_OBJECTS:%=obj/%) \
	  -o release-search -lz3

PROFILES = $(PROFILE_ARGS:%=PROFILE-%)

$(PROFILES): PROFILE-%: profile-search
	cp ../../results/translate/$(PROFILE_TASK)/all.groups .
	./profile-search $* < ../../results/preprocess/$(PROFILE_TASK)/output
	gprof profile-search | ./cleanup-profile > $@

$(OBJECTS): %.o: %.cc
	$(CC) $(CCOPT) -c $< -o obj/$@ 

$(PROFILE_OBJECTS): %.profile.o: %.cc
	$(CC) $(CCOPT) $(PROFOPT) -c $< -o obj/$@

$(RELEASE_OBJECTS): %.release.o: %.cc
	$(CC) $(RELEASEOPT) -c $< -o obj/$@ 

clean:
	rm -f $(OBJECTS:%=obj/%) $(PROFILE_OBJECTS:%=obj/%) $(RELEASE_OBJECTS:%=obj/%) *~ *.pyc
	rm -f Makefile.depend profile-search gmon.out PROFILE core
	rm -f sas_plan

veryclean: clean
	rm -f search

Makefile.depend: $(SOURCES) $(HEADERS)
	$(DEPEND) $(SOURCES) > Makefile.temp
	sed -e "s/\(.*\)\.o:\(.*\)/\1.profile.o:\2/" Makefile.temp >> Makefile.temp2
	cat Makefile.temp Makefile.temp2 > Makefile.depend
	rm -f Makefile.temp Makefile.temp2

ifneq ($(MAKECMDGOALS),clean)
ifneq ($(MAKECMDGOALS),veryclean)
-include Makefile.depend
endif
endif

.PHONY: release clean veryclean
