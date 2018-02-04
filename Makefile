TARGET = ecpp-dj
CC = g++
CXX = g++ -std=c++14 
DEFINES = -DSTANDALONE -DSTANDALONE_ECPP -DUSE_CM -DMAX_THREADS=8
CFLAGS = -O3 -g -Wall -Wno-literal-suffix $(DEFINES)
LIBS = /usr/lib/x86_64-linux-gnu/libgmp.a -lm -lpthread -lcm_class -lcm_common -lmpfpx

OBJ = ecpp.o bls75.o aks.o primality.o ecm.o prime_iterator.o gmp_main.o \
      factor.o squfof126.o pbrent63.o tinyqs.o \
      real.o isaac.o random_prime.o utility.o expr.o
HEADERS = ptypes.h class_poly_data.h

.PHONY: default all clean

default: $(TARGET) vcert
all: default

%.o: %.c $(HEADERS)
	$(CC) $(CFLAGS) -c $< -o $@

%.o: %.cpp $(HEADERS)
	$(CXX) $(CFLAGS) -c $< -o $@

.PRECIOUS: $(TARGET) $(OBJECTS)

$(TARGET): $(OBJ)
	$(CXX) $^ $(LIBS) -o $@

vcert: vcert.o
	$(CC) $^ $(LIBS) -o $@

clean:
	-rm -f *.o

realclean distclean: clean
	-rm -f $(TARGET) vcert

TEST1 = 11739771271677308623
TEST2 = 4101186565771483058393796013015990306873
TEST3 = 35393208195490503043982975376709535956301978008095654379254570182486977128836509
TEST4 = 935006864223353238737221824562525122013245238547726726389470209512876196672409305516259055214126542251267716102384835899
TEST5 = 25433248801892216938808041984973587415848723989586550342338936524369752729114437550630504573611493987544033285909689162724975971196674890122730486522513928304389686931651745712950504486324914805161849
TEST6 = 9805395078382368090505040572030888128042903590778595659611793383233089744266057832338719254777179628060930905633717264804767081354556273122188172463117096876389627469817121375789418174467686118164854924603273433083668455457307317475867158494243611475656192285904836693990000951833
TEST7 = 14783869341310731862535181711924146413209106702463668486125206627959998111552028525869806779180480078890581625378293879184823213870417286554264959032457904699577075117266041686053691857746703656877556879868345571593862758480658145938864170620882703502631810038072518245192559323694333232320523172244347200606659255752705575709361904749964234503630803
TEST8 = 516069211402263086362802849056712149142247708608707602810064116323740967320507238792597022510888972176570219148745538673939283056074749627707686516295450338874349093022059487090007604327705115534233283204877186839852673049019899452650976370088509524263064316558360307931746214148027462933967332118502005274436360122078931230288854613802443446620402918656243749843390157467993315073584216791188709452340255395988925217870997387615378161410168698419453325449311
TEST9 = 117601040412545488514832413116124654778643679623834232691474159193304815625021545381522192459893594348968456387395033424865177139368803482525166479020381057434366792463275689281202125306028624960617019082960990646966356143260160461111142482490769090260594633448600049003889907700916419839169742848389034604555998596743620210272378467145433654999754884748803873102065426685371983000066160925714427517314165484460091357139845925112169581720066339676729745002919539368943410554224770005026505867682460046849254142878380362566634540250211808024291810544534257406802029413447696395850193424469333538571953351132249312743123835534837496352990395576511774079971493584358654960260785531223192373024746789709358700703205420736845321419521689467096522901574359748626009828882402745726289882974975272630855759996221989590295515027457

test: $(TARGET) vcert
	@for n in $(TEST1) $(TEST2) $(TEST3) $(TEST4) $(TEST5) $(TEST6) $(TEST7) $(TEST8); do echo -n "$${#n} digits ..."; ./ecpp-dj -c $$n | ./vcert -q -; if [ $$? -eq 0 ]; then echo "Pass"; else echo "FAIL"; fi; done

test2: $(TARGET) vcert
	./ecpp-dj -c $(TEST9) | ./vcert -q -; if [ $$? -eq 0 ]; then echo "Pass"; else echo "FAIL"; fi

TEST10 = 253994993772556144681481010720028685865753024611253957377279611592149502034781850559104427660009746331875226567181181809805187854163113525834821026684987678338245748687611366613136255749263346751834763562182693780303511900728921710319082135553144350760139859309389636368551922834059407843294133087784980216603151545408536909551113728190519123362404346644195679473685240255808595294293236181890525021530984351030871227684338786425144572278836876684867231441134894225271250857920712885837571258379313836323074865947686993269727757

perf: $(TARGET)
	/bin/bash -c "time ./ecpp-dj -t 8 $(TEST10)"
