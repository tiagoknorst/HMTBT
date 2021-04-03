#include "cpu/exetrace.hh"

#include <iomanip>

#include "arch/isa_traits.hh"
#include "arch/utility.hh"
#include "base/loader/symtab.hh"
#include "cpu/o3/fetch.hh"
#include "cpu/o3/fetch.cc"
#include "config/the_isa.hh"
#include "cpu/base.hh"
#include "cpu/static_inst.hh"
#include "cpu/thread_context.hh"
#include "debug/ExecAll.hh"
#include "debug/AnalysisFlag.hh"
#include "debug/ResultsFlag.hh"
#include "enums/OpClass.hh"
#include <string>
#include <iostream>
#include <sstream>
#include <iterator>
#include <fstream>

//180 nm RTL
//#define POWER_DSA     701720000000     // (pw)
//15 nm (suposicao)
#define POWER_DSA      32459907462     // (pw)

//15 nm RTL
#define POWER_DIM      32459907462     // (pw)
#define POWER_CGRA     61215364740     // (pw)
#define POWER_INTALU     671381110     // (pw)
#define POWER_INTMUL    2717287740     // (pw)
#define POWER_MEMACC     721421530     // (pw)

//14 nm FinCACTI
#define POWER_CACHE_L_4K  34023800     // (pw)
#define POWER_CACHE_W_4K 836329820     // (pw)
#define POWER_CACHE_R_4K 930626731     // (pw)


#define EXECUCAO 0
#define ARQUIVO 1

#define REMOVESYSCALLS 0


#define MUTUALEXECUTION 1
#define TABLEDECISION 1


#define LOOPDETECTION           0   // maquina de estados (nao implementada ainda)
#define DATACOLLECTION          1
#define DEPENDENCYANALYSIS      2
#define STOREIDEXECUTION        3
#define MAPPING                 4
#define SPECULATIVEEXECUTION    5

#define CLOCKPERIOD 1000    // (ps)
#define ARRAYMAPSIZE 64     // (speculative iterations)
#define CACHESIZE 2        // (loops)          DEFAULT=16

#define n 16                // (cgra configs)   DEFAULT=32

//    Delay de acesso a cache (em ciclos de clock)
//DSA cache is 8KB and verification is 1KB
#define CACHE_HIT_DELAY 1       //TODO: atualizar valores
#define CACHE_MISS_DELAY 1
#define CACHE_WRITE_DELAY 1
#define CACHE_READ_DELAY 1


#define nconfigs 700
#define nloops 100


//int CACHESIZE, 
int NEONREGS, readPar=1;

//VARIAVEIS DSA

typedef struct {
    long long int data;
    int rd1,rd2, rs1,rs2,rs3,rs4;
} InstReg;

InstReg InstRegs;
InstReg PrevRegs;


typedef struct {
    Addr firstAddress, lastAddress, storeInstAddress, storeDataAddress;

    int executions, iterations, storeRegister, storeDataSize;
    long long int predictedSize, sequentialExecTime, iterationTimeSimd, detectionLatency;
    
    bool analyzed, discarded, vectorizable, definedSize, conditional, dynamicRange;
    
    int neonInst, condInst, totalInst;
    long long int procExecTime;
} LoopInfo;

LoopInfo loops[CACHESIZE];


Trace::CacheMemory DSACache(CACHE_WRITE_DELAY, CACHE_READ_DELAY, CACHE_MISS_DELAY);   // 2KB cache
Trace::CacheMemory VerificationCache(CACHE_WRITE_DELAY, CACHE_READ_DELAY, 0);         // 1KB cache
Trace::CacheMemory BTCGRACache(CACHE_WRITE_DELAY, CACHE_READ_DELAY, CACHE_MISS_DELAY);  // 2KB cache
Trace::CacheMemory HistoryTable(CACHE_WRITE_DELAY, CACHE_READ_DELAY, CACHE_MISS_DELAY);


typedef struct {
    std::string instType;
    int simdLatency;
    long long int cont;
    long long int simdCont;
} InstLat;

InstLat InstLatency[12];
InstLat LoopTempLatency[12];


typedef struct {
    Addr cmpsAddress;
    long long int cmpsOp1, cmpsOp2;
    long long int iterationTimeSimd;
    
    bool enable;
} LoopAnalyze;

LoopAnalyze LoopAnalysis;


bool inicialization=1, printResults=1, cacheFull=0;
bool instCond, instSetFlag, instCmp, instBranchSubRoutine, instMicro, controlInst, thereIsConstant;
bool branchOccurence=0, syscallOccurence=0;
bool nonVectExecuting=0;

long long int ticks_sequential_count= 0, ticks_parallel_count = 0;
long long int ticks_sequential_dynamicrange = 0, ticks_parallel_dynamicrange = 0;
long long int ticks_sequential_sentinel = 0, ticks_parallel_sentinel = 0;
long long int ticks_sequential_conditional = 0, ticks_parallel_conditional = 0;
long long int ticks_sequential_sentcond = 0, ticks_parallel_sentcond = 0;
long long int ticks_sequential_dynamiccond = 0, ticks_parallel_dynamiccond = 0;
long long int ticks_sequential_nonvect = 0;

short int i, j, k, f, currentLoop=0, currentState=LOOPDETECTION; 
long long int detectionLatency=0;
long long int economiaDSAcount=0, economiaDSAdynamicrange=0, economiaDSAsentinel=0, economiaDSAconditional=0, economiaDSAdynamiccond=0, economiaDSAsentcond=0;
long long int economiaDSAcount_syscall=0, economiaDSAsentinel_syscall=0, economiaDSAconditional_syscall=0, economiaDSAsentcond_syscall=0;
long long int constante, loop_count=0, loop_dynamicrange=0, loop_sentinel=0, loop_cond=0, loop_dynamiccond=0, loop_sentcond=0, loop_funct=0;

long long int currentTick=0, previousTick=0, syscalltime=0, syscalltotals=0;


Addr instAddress, prevInstAddress, dataAddress, regContent[64];
Addr nonVectFirstAddress, nonVectLastAddress;

std::string fullInstruction, instruction, prevInst, instType, prevInstType;


Addr programCounter;
std::string funct, previousFunct;



//VARIAVEIS DIM

//const int n = 32; //800
const int column_number = 18;
///*
const int line_number = 8;
const int mem_line = 2;
const int mult_line = 5;
const int float_line = 6;
//*/
/*
const int line_number = 100;
const int mem_line = 30;
const int mult_line = 60;
const int float_line = 80;
//*/
const int reg_per_cycle = 4;
const int num_regs_proc = 64;

int specDeep = 0, indice_menor = 0, decreaseCycle = 0, oneConfigCycles = 0, totalCycles = 0, arrayCycle = 0, index_hit = 0;
long long int difTick = 0, finTick = 0, auxinTick = 0, auxfinTick = 0, inTick = 0, condinstCount = 0;
bool firsttime = 0, configurationHit = 0, initArray = 0, endArray = 0, init_conf = 0;
bool branchInstruction = 0, previousWasBranch = 0, configStart = 0, arrayFull = 0, conditionalInstruction = 0;
bool regRead[num_regs_proc], regWrite[num_regs_proc], specregRead[num_regs_proc], specregWrite[num_regs_proc], contregRead[num_regs_proc], contregWrite[num_regs_proc];
Addr lastID = 0, savlastID = 0;
int contadorWb = 0, contadorSr = 0, wbCycles = 0, srCycles = 0;

struct arrayMap{
   Addr afterbranchId;
   int registersMap[num_regs_proc];
   int arrayMatrix[line_number][column_number];
};

struct arrayMemory{
   Addr afterbranchId;
   Addr lastID;
   int arrayMatrix[line_number][column_number];
   int lastAllocatedColumn;
   bool readReg[num_regs_proc];
   bool writeReg[num_regs_proc];
   long long int inTick;
   long long int finTick;
   long long int configCycles;
   int specDeep;
   long long int accesses;
   struct arrayMemory *next;
   
   Addr lastInstId;
   bool continues;
   long long int lastHitTick;
};

arrayMap arrMap;

arrayMemory *memoriaConfig = new arrayMemory[n];


//STATISTICS FLAGS
long long int economiaTotal = 0;
long long int economiaTotalDLP = 0;
long long int greatIndividualEconomy = 0;
long long int totalHits= 0;
long long int totalcontBlocks = 0;
long long int totalConfigs = 0;
long long int totalInst = 0;
long long int totalCond = 0;
long long int totalALU = 0;
long long int totalMEM = 0;
long long int totalOther = 0;
long long int totalTick = 0;

bool continues = 0;
double totalEnergyCGRA = 0;

int executionLoopID;
Addr addrendDLP = 0;


typedef struct {
    Addr address;
    long long int arrayTime, dsaTime;
} InterTable;

bool executaDLP = 0, executaILP = 0, lido=0;
int currentConfig = 0, stateIntersection = 0, lastStateIntersection = 0;
long long int procTotalTicks, dsaTotalTicks, arrayTotalTicks, bothTotalTicks, stateChangeTick = 0, lastInterIdx=0;
long long int dsaWins=0, arrayWins=0;
double dsaWinsPerc=0, arrayWinsPerc=0, loopOnArrayAvgIPC=0, loopOnDSAAvgParallelism=0;

InterTable intersectionTable[64];


long long int contador=0, analisisWastedTicks=0, tempAnalisisWastedTicks=0;
long long int randomFunctTicks=0, printFunctTicks=0, inmainTicks=0, tempDif=0, tempDifAcc=0, prevWhen=0;
bool interseccao=0;

typedef struct {
    long long int address;
    long long int economy;
} EconomyRanking;

EconomyRanking greatestTotalEconomiesDLP[nloops];
EconomyRanking greatestTotalEconomiesILP[nconfigs];



using namespace std;
using namespace TheISA;

namespace Trace {

void insereValorNoVetor(EconomyRanking *greatestTotalEconomies, int range, Addr address, long long int economy);

void Trace::ExeTracerRecord::traceInst(const StaticInstPtr &inst, bool ran)
{
    //imprimeTracePadrao(inst, ran);
    //imprimeTraceInjetorVHDL(inst, ran);
    
    //DPRINTF(AnalysisFlag, "Data size: %lld\n", getSize());
    
    monitoraFuncoes(inst);
    
    if(readPar)
        leituraDeParametros();
    
    if(ran){
        extraiDadosDoTrace(inst, ran, EXECUCAO);
        
        if(!REMOVESYSCALLS || (REMOVESYSCALLS && !syscallOccurence)){
            exploracaoDLP();
            exploracaoILP();
        }
    }
    
    
    // EXECUCAO LENDO ARQUIVO TRACE
    /* 
    extraiDadosDoTrace(inst, ran, ARQUIVO);
    
    if(!lido)
        leituraDeArquivo();
    */
    
    //analiseDeInterseccao();
}

void insereValorNoVetor(EconomyRanking *greatestTotalEconomies, int range, Addr address, long long int economy){
    int i;
    
    //Insere no vetor
    for(i=0; i<range; i++){
        if(address == 0 && economy == 0){
            greatestTotalEconomies[i].address = 0;
            greatestTotalEconomies[i].economy = 0;
        }
        else if(address == greatestTotalEconomies[i].address){
            greatestTotalEconomies[i].economy += economy;
            
            break;
        }
        else if(greatestTotalEconomies[i].address == 0){
            greatestTotalEconomies[i].address = address;
            greatestTotalEconomies[i].economy = economy;
            
            break;
        }
    }
    
    //Politica de substituicao
    if(i == range && economy != 0){
        int substitute = 0, lowest = greatestTotalEconomies[0].economy;
        
        for(i=1; i<range; i++){
            if(greatestTotalEconomies[i].economy < lowest){
                lowest = greatestTotalEconomies[i].economy;
                substitute = i;
            }
        }
        
        greatestTotalEconomies[substitute].address = address;
        greatestTotalEconomies[substitute].economy = economy;
        
        //DPRINTF(ResultsFlag, "Substituicao\n");
    }
}

void Trace::ExeTracerRecord::exploracaoDLP(){
    inicializaVariaveisDeLatencia();
    
    bool encontrado=0;
    
    if(nonVectExecuting){
        if(instAddress < nonVectFirstAddress || instAddress > nonVectLastAddress){
            nonVectExecuting = 0;
        }
        else{
            ticks_sequential_nonvect += (currentTick - previousTick);
        }
    }
    
    if(branchOccurence){
        branchOccurence=0;
        
        DPRINTF(AnalysisFlag, "branchOccurence\n");
        
        //Branch taken (possivel loop)
        if(instAddress < prevInstAddress){
            DPRINTF(AnalysisFlag, "Branch taken\n");
            
            //Busca loop na cache
            for(i=0; i<CACHESIZE; i++){
                //Loop ID dado pelo endereco da ultima instrucao do loop
                if(loops[i].lastAddress == prevInstAddress){
                    encontrado = 1;   //CACHE HIT
                    DSACache.read();
                    loops[i].iterations++;
                    
                    DPRINTF(AnalysisFlag, "LOOP CACHE HIT\n");
                    
                    if(loops[i].discarded){
                        DPRINTF(AnalysisFlag, "LOOP anteriormente descartado\n");
                    }
                    //Reaproveitamento de loops previamente analisados
                    else if(loops[i].analyzed){
                        DSACache.read();
                        if(loops[i].vectorizable){
                            if(!executaDLP){
                                executaDLP = 1;
                                
                                loops[i].sequentialExecTime = currentTick;
                                
                                currentLoop = i;
                                
                                DPRINTF(AnalysisFlag, "Endereco inicial: %#x\n", instAddress);
                                DPRINTF(AnalysisFlag, "Endereco final: %#x\n", prevInstAddress);
                                DPRINTF(AnalysisFlag, "currentLoop: %d\n", currentLoop);
                            }
                            else{
                                DPRINTF(AnalysisFlag, "WARNING: OUTRO LOOP EM EXECUCAO\n");
                            }
                        }
                        else{
                            DPRINTF(AnalysisFlag, "Loop nao vetorizavel\n");
                            
                            nonVectExecuting = 1;
                            nonVectFirstAddress = loops[i].firstAddress;
                            nonVectLastAddress  = loops[i].lastAddress;
                        }
                    }
                    // DATACOLLECTION
                    else if(loops[i].iterations == 2){
                        //Contabilizacao do tempo de execucao SIMD
                        loops[i].iterationTimeSimd = LoopAnalysis.iterationTimeSimd;
                        
                        DPRINTF(AnalysisFlag, "iterationTimeSimd %d\n", loops[i].iterationTimeSimd);
                                                
                        //Logica de previsao de tamanho (inicio)
                        
                        VerificationCache.read();
                                                
                        if(LoopAnalysis.cmpsAddress > instAddress && LoopAnalysis.cmpsAddress < prevInstAddress){
                            DPRINTF(AnalysisFlag, "Cmps dentro do range do loop\n");
                            
                            //Cmps dentro do range do loop
                            loops[i].definedSize = 1;
                            loops[i].predictedSize = LoopAnalysis.cmpsOp1;
                            
                            DPRINTF(AnalysisFlag, "loops[%d].predictedSize = %d (cmpsOp1)\n", i, loops[i].predictedSize);
                        }
                        else{
                            DPRINTF(AnalysisFlag, "Loop de tam indefinido\n");
                            
                            //Loop de tam indefinido
                            loops[i].definedSize = 0;
                        }
                        
                        tempAnalisisWastedTicks = currentTick;
                    }
                    // DEPENDENCYANALYSIS
                    else if(loops[i].iterations == 3){
                        //Fim da etapa de analise do loop
                        LoopAnalysis.enable = 0;
                        loops[i].analyzed = 1;
                        
                        VerificationCache.read();
                        DSACache.write();
                        
                        //Contabilizacao do tempo de analise
                        detectionLatency += currentTick - loops[i].detectionLatency;
                        ///*
                        //Caso falhe a deteccao do tamanho do dado, tamanho padrao = 32 bits
                        if(loops[i].storeDataSize != 8 && loops[i].storeDataSize != 4
                                                       && loops[i].storeDataSize != 2
                                                       && loops[i].storeDataSize != 1){
                            DPRINTF(AnalysisFlag, "Tamanho do dado desconhecido: %d\n", loops[i].storeDataSize);
                            
                            loops[i].storeDataSize = 4;
                        }
                        //*/
                        
                        //Logica de previsao de tamanho (fim)
                        if(loops[i].definedSize){
                            //Calculo da previsao
                            if((LoopAnalysis.cmpsOp1 - loops[i].predictedSize) != 0){
                                loops[i].predictedSize = (LoopAnalysis.cmpsOp2 - LoopAnalysis.cmpsOp1) / (LoopAnalysis.cmpsOp1 - loops[i].predictedSize);
                                loops[i].predictedSize += 3;
                                
                                DPRINTF(AnalysisFlag, "LoopAnalysis.cmpsOp1 = %d\n", LoopAnalysis.cmpsOp1);
                                DPRINTF(AnalysisFlag, "LoopAnalysis.cmpsOp2 = %d\n", LoopAnalysis.cmpsOp2);
                                DPRINTF(AnalysisFlag, "Tamanho previsto %d\n", loops[i].predictedSize);
                                
                                if(loops[i].predictedSize >= 4){
                                    DPRINTF(AnalysisFlag, "Previsao ok\n");
                                    
                                    //Vetorizacao
                                    if(loops[i].vectorizable){
                                        executaDLP = 1;
                                        
                                        DPRINTF(AnalysisFlag, "Vetorizavel\n");
                                        
                                        loops[i].sequentialExecTime = currentTick;
                                    }
                                }
                                else{
                                    loops[i].definedSize = 0;
                                    
                                    DPRINTF(AnalysisFlag, "Movido para analise de tam indefinido\n");
                                }
                            }
                            else{
                                DPRINTF(AnalysisFlag, "Divisao por zero! op1/op2: %d/%d\n", LoopAnalysis.cmpsOp1, loops[i].predictedSize);
                                
                                loops[i].definedSize = 0;
                            }
                        }
                    }
                    
                    // Remocao do loop da cache
                    else if(loops[i].executions != 0){
                        //Loop nao analisado na primeira execucao
                        DSACache.write();
                        
                        currentLoop = i;
                        
                        LoopAnalysis.enable = 1;
                        LoopAnalysis.iterationTimeSimd = 0;
                        loops[i].predictedSize = 0;
                        loops[i].definedSize = 0;
                        loops[i].conditional = 0;
                        loops[i].dynamicRange = 0;
                        loops[i].analyzed = 0;
                        loops[i].discarded = 0;
                        loops[i].vectorizable = 1;
                        loops[i].storeInstAddress = 0;
                        loops[i].storeDataAddress = 0;
                        loops[i].storeDataSize = 0;
                        loops[i].storeRegister = 99;
                    }
                    
                    if(loops[i].iterations == 4)
                        tempAnalisisWastedTicks = 0;
                    
                    break;  //Interrompe busca na cache apos hit
                }
            }
            //CACHE MISS! Registra novo loop
            if(!encontrado){
                DSACache.miss();
                
                encontrado=0;
                
                armazenaLoopNaCache();
            }
        }
        //Branch not taken (termino do loop)
        else if((instAddress - prevInstAddress) == 4 && prevInstAddress == loops[currentLoop].lastAddress)
            terminoDoLoop();
    }
    
    else if(LoopAnalysis.enable){
        if(!(((instAddress-prevInstAddress)==4) || (instAddress == prevInstAddress))){
            descarteDeLoops();
            
            DPRINTF(AnalysisFlag, "Descartando loop %d (descontinuo)\n", currentLoop);
        }
        else if(instCond && instruction[0]!='b'){
            loops[currentLoop].conditional = 1;
        }
    }
    
    
    //Registra a ocorrencia de possivel loop
    if(instruction[0]=='b')
        verificaBranchs();
    
    salvaDadosCmps();
    
    if(LoopAnalysis.enable)
        analiseDeDependencias();
}




void Trace::ExeTracerRecord::armazenaLoopNaCache()
{
    bool encontrado=0;
    
    //Busca enderecos vazios na cache de loops
    for(i=0; i<CACHESIZE; i++){
        if(!loops[i].analyzed){
            encontrado=1;
            currentLoop=i;
            break;
        }
    }
    //Politica de substituicao da cache de loops
    if(!encontrado){
        //cacheFull=1;
        
        for(i=0; i<CACHESIZE; i++){
            if(loops[i].discarded){
                encontrado=1;
                currentLoop=i;
                break;
            }
        }
        if(!encontrado){
            for(i=0; i<CACHESIZE; i++){
                if(!loops[i].vectorizable){
                    encontrado=1;
                    currentLoop=i;
                    break;
                }
            }
            if(!encontrado){
                currentLoop = (currentLoop+1) % CACHESIZE;
                
                cacheFull=1;
            }
        }
    }
    
    LoopAnalysis.enable = 1;
    LoopAnalysis.iterationTimeSimd = 0;
    
    loops[currentLoop].firstAddress = instAddress;
    loops[currentLoop].lastAddress = prevInstAddress;
    loops[currentLoop].sequentialExecTime = currentTick;
    loops[currentLoop].detectionLatency = currentTick;
    loops[currentLoop].executions = 0;
    loops[currentLoop].iterations = 1;
    loops[currentLoop].predictedSize = 0;
    loops[currentLoop].definedSize = 0;
    loops[currentLoop].conditional = 0;
    loops[currentLoop].dynamicRange = 0;
    loops[currentLoop].analyzed = 0;
    loops[currentLoop].discarded = 0;
    loops[currentLoop].vectorizable = 1;
    loops[currentLoop].storeInstAddress = 0;
    loops[currentLoop].storeDataAddress = 0;
    loops[currentLoop].storeDataSize = 0;
    loops[currentLoop].storeRegister = 99;
    
    DPRINTF(AnalysisFlag, "LOOP CACHE MISS\n");
    DPRINTF(AnalysisFlag, "Endereco inicial: %#x\n", instAddress);
    DPRINTF(AnalysisFlag, "Endereco final: %#x\n", prevInstAddress);
    DPRINTF(AnalysisFlag, "currentLoop: %d\n", currentLoop);
}


void Trace::ExeTracerRecord::terminoDoLoop()
{
    loops[currentLoop].iterations++;
    loops[currentLoop].executions++;
    
    DPRINTF(AnalysisFlag, "LOOP FINALIZADO!  nº %d (%#x)\n", currentLoop, loops[currentLoop].lastAddress);
    DPRINTF(AnalysisFlag, "Tamanho previsto: %d\n", loops[currentLoop].predictedSize);
    DPRINTF(AnalysisFlag, "Tamanho de fato: %d\n", loops[currentLoop].iterations);
    
    if(loops[currentLoop].definedSize && loops[currentLoop].predictedSize != loops[currentLoop].iterations){
        loops[currentLoop].definedSize = 0;
        
        DPRINTF(AnalysisFlag, "Errou a previsao! (Previu %d e ocorreram %d\n", loops[currentLoop].predictedSize, loops[currentLoop].iterations);
        
        if((loops[currentLoop].predictedSize < 100*loops[currentLoop].iterations) && (loops[currentLoop].iterations < 100*loops[currentLoop].predictedSize)){
            loops[currentLoop].dynamicRange = 1;
            
            DPRINTF(AnalysisFlag, "Dynamic Range loop!\n");
        }
    }
    if(!loops[currentLoop].definedSize && loops[currentLoop].iterations > 3){
        detectionLatency += 2*CLOCKPERIOD * (loops[currentLoop].iterations-3);
        
        //Preve o numero de iteracoes da proxima execucao
        loops[currentLoop].predictedSize = loops[currentLoop].iterations;
    }
    
    //Registra ganho SIMD
    if(loops[currentLoop].vectorizable && loops[currentLoop].analyzed)
        contabilizaEconomia();
    
    DPRINTF(AnalysisFlag, "Instrucoes SIMD: %d\n", loops[currentLoop].neonInst);
    DPRINTF(AnalysisFlag, "Instrucoes condicionais: %d\n", loops[currentLoop].condInst);
    DPRINTF(AnalysisFlag, "Tempo processador: %d\n", loops[currentLoop].procExecTime);
    
    
    DSACache.write();
    loops[currentLoop].iterations = 0;
}


void Trace::ExeTracerRecord::contabilizaEconomia()
{
    long long int countLoopEconomy=0, dynamicrangeLoopEconomy=0, sentinelLoopEconomy=0;
    long long int conditionalLoopEconomy=0, dynamiccondLoopEconomy=0, sentcondLoopEconomy=0;
    long long int iterationsSisd, stall=0;
    
    if(loops[currentLoop].executions == 1)
        iterationsSisd = (loops[currentLoop].predictedSize - 3);
    else
        iterationsSisd = (loops[currentLoop].predictedSize - 1);
    
    int parallelism = (16 / loops[currentLoop].storeDataSize);
    int iterationsSimd = (iterationsSisd / parallelism);
    
    if((iterationsSisd % parallelism) != 0)
        iterationsSimd++;
    
    //stall computing
    if(loops[currentLoop].neonInst > NEONREGS){
        if((loops[currentLoop].procExecTime * parallelism) > (NEONREGS * CLOCKPERIOD)){
            stall = (loops[currentLoop].procExecTime * parallelism) - (NEONREGS * CLOCKPERIOD);

            DPRINTF(AnalysisFlag, "neonInst > NEONREGS, stall: %d\n", stall);
        }
    }
    else{
        if((loops[currentLoop].procExecTime * parallelism) > loops[currentLoop].iterationTimeSimd){
            stall = (loops[currentLoop].procExecTime * parallelism) - loops[currentLoop].iterationTimeSimd;

            DPRINTF(AnalysisFlag, "neonInst < NEONREGS, stall: %ld\n", stall);
        }
    }
    
    long long int sequentialExecTime = currentTick - loops[currentLoop].sequentialExecTime;
    long long int parallelExecTime = (loops[currentLoop].iterationTimeSimd * iterationsSimd);
    long long int parallelSpeculativeExecTime = parallelExecTime + (stall * iterationsSimd);
    long long int overdoneExecution = 0;
    
    DPRINTF(AnalysisFlag, "iterationsSimd:       %lli\n", iterationsSimd);
    DPRINTF(AnalysisFlag, "iterationTimeSimd:    %lli\n", loops[currentLoop].iterationTimeSimd);
    DPRINTF(AnalysisFlag, "sequentialExecTime:   %lli\n", sequentialExecTime);
    DPRINTF(AnalysisFlag, "parallelExecTime:     %lli\n", parallelExecTime);
    DPRINTF(AnalysisFlag, "parallelSpecExecTime: %lli\n", parallelSpeculativeExecTime);
    
    
    if(loops[currentLoop].definedSize){
        if(!loops[currentLoop].conditional){
            loop_count++;
            
            //economiaDSA += sequentialExecTime - parallelExecTime - CACHE_HIT_DELAY*CLOCKPERIOD;
            countLoopEconomy = sequentialExecTime - (parallelExecTime + CACHE_HIT_DELAY*CLOCKPERIOD);
            DPRINTF(AnalysisFlag, "Ticks economizados (countLoop): %lli\n", countLoopEconomy);
            
            
            ticks_parallel_count += parallelExecTime;
            ticks_sequential_count+= sequentialExecTime;
        }
        else{
            loop_cond++;
            
            //economiaDSA += sequentialExecTime - parallelExecTime - CACHE_HIT_DELAY*CLOCKPERIOD;
            conditionalLoopEconomy = sequentialExecTime - (parallelSpeculativeExecTime + CACHE_HIT_DELAY*CLOCKPERIOD);
            DPRINTF(AnalysisFlag, "Ticks economizados (conditionalLoop): %lli\n", conditionalLoopEconomy);
            
            
            ticks_parallel_conditional += parallelSpeculativeExecTime;
            ticks_sequential_conditional += sequentialExecTime;
        }
    }
    else{
        if(loops[currentLoop].dynamicRange){
            if(!loops[currentLoop].conditional){
                loop_dynamicrange++;
                
                ticks_sequential_dynamicrange += sequentialExecTime;
                
                //DPRINTF(ResultsFlag, "ticks_sequential_sentinel += %lli\n", sequentialExecTime);
                
                if(loops[currentLoop].executions > 1){
                    dynamicrangeLoopEconomy = sequentialExecTime - (parallelSpeculativeExecTime + CACHE_HIT_DELAY*CLOCKPERIOD);
                    DPRINTF(AnalysisFlag, "Ticks economizados (dynamicrangeLoop): %lli\n", sequentialExecTime - parallelSpeculativeExecTime - CACHE_HIT_DELAY*CLOCKPERIOD);
                    
                    ticks_parallel_dynamicrange += parallelSpeculativeExecTime;
                }
            }
            else{
                loop_dynamiccond++;
                
                ticks_sequential_dynamiccond += sequentialExecTime;
                
                //DPRINTF(ResultsFlag, "ticks_sequential_sentinel += %lli\n", sequentialExecTime);
                
                if(loops[currentLoop].executions > 1){
                    dynamiccondLoopEconomy = sequentialExecTime - (parallelSpeculativeExecTime + CACHE_HIT_DELAY*CLOCKPERIOD);
                    DPRINTF(AnalysisFlag, "Ticks economizados (dynamiccondLoop): %lli\n", sequentialExecTime - parallelSpeculativeExecTime - CACHE_HIT_DELAY*CLOCKPERIOD);
                    
                    ticks_parallel_dynamiccond += parallelSpeculativeExecTime;
                }
            }
        }
        else{
            if(!loops[currentLoop].conditional){
                loop_sentinel++;
                
                ticks_sequential_sentinel += sequentialExecTime;
                
                //DPRINTF(ResultsFlag, "ticks_sequential_sentinel += %lli\n", sequentialExecTime);
                
                if(loops[currentLoop].executions > 1){
                    sentinelLoopEconomy = sequentialExecTime - (parallelSpeculativeExecTime + CACHE_HIT_DELAY*CLOCKPERIOD);
                    DPRINTF(AnalysisFlag, "Ticks economizados (sentinelLoop): %lli\n", sequentialExecTime - parallelSpeculativeExecTime - CACHE_HIT_DELAY*CLOCKPERIOD);
                    
                    ticks_parallel_sentinel += parallelSpeculativeExecTime;
                }
            }
            else{
                loop_sentcond++;
                
                ticks_sequential_sentcond += sequentialExecTime;
                
                //DPRINTF(ResultsFlag, "ticks_sequential_sentinel += %lli\n", sequentialExecTime);
                
                if(loops[currentLoop].executions > 1){
                    sentcondLoopEconomy = sequentialExecTime - (parallelSpeculativeExecTime + CACHE_HIT_DELAY*CLOCKPERIOD);
                    DPRINTF(AnalysisFlag, "Ticks economizados (sentinelLoop): %lli\n", sequentialExecTime - parallelSpeculativeExecTime - CACHE_HIT_DELAY*CLOCKPERIOD);
                    
                    ticks_parallel_sentcond += parallelSpeculativeExecTime;
                }
            }
        }
    }
    
    //Não contabiliza a economia caso o array tenha preemptado a execucao da DSA
    if(executaDLP){
        economiaDSAcount += countLoopEconomy;
        economiaDSAdynamicrange += dynamicrangeLoopEconomy;
        economiaDSAsentinel += sentinelLoopEconomy;
        economiaDSAconditional += conditionalLoopEconomy;
        economiaDSAdynamiccond += dynamiccondLoopEconomy;
        economiaDSAsentcond += sentcondLoopEconomy;
        
        if(funct[0]=='_' && funct[1]!='Z'){
            economiaDSAcount_syscall += countLoopEconomy;
            economiaDSAsentcond_syscall += sentcondLoopEconomy;
        }
        
        
        if((iterationsSisd % parallelism) == 0){
            for(i=0; i<12; i++){
                InstLatency[i].simdCont += (LoopTempLatency[i].cont / parallelism);
            }
        }
        else{
            for(i=0; i<12; i++){
                if(LoopTempLatency[i].cont > 0)
                    InstLatency[i].simdCont += (LoopTempLatency[i].cont / parallelism) + 1;
            }
        }
        
        if(InstLatency[11].simdCont > 0){
            DPRINTF(ResultsFlag, "InstLatency[11].simdCont: %d\n", InstLatency[11].simdCont);
        }
        
        for(i=0; i<12; i++){
            LoopTempLatency[i].cont = 0;
        }
        
        executaDLP = 0;
        
        
        insereValorNoVetor(greatestTotalEconomiesDLP, nloops, loops[currentLoop].firstAddress, countLoopEconomy+sentinelLoopEconomy+conditionalLoopEconomy+sentcondLoopEconomy);
    }
    
    // ATUALIZACAO DA TABELA COM VALOR REAL DO TEMPO DE EXECUCAO DE UMA ITERACAO (EQUIVALENTE SISD)
    bool encontrado=0;
    
    for(i=0; i<64; i++){
        if(loops[currentLoop].firstAddress == intersectionTable[i].address){
            encontrado=1;
            break;
        }
    }
    
    if(encontrado){
        DPRINTF(AnalysisFlag, "Tabela atualizada (loop: %lld):\n", loops[currentLoop].firstAddress);
        DPRINTF(AnalysisFlag, "Antes: %lld\n", intersectionTable[i].dsaTime);
        
        
        
        if(loops[currentLoop].executions == 1){
            intersectionTable[i].dsaTime = (parallelExecTime + overdoneExecution) / iterationsSisd;
        }
        else{
            long long int currentExecTime = (parallelExecTime + overdoneExecution) / iterationsSisd;
            intersectionTable[i].dsaTime = ((intersectionTable[i].dsaTime * loops[currentLoop].executions) + currentExecTime) / (loops[currentLoop].executions+1);
        }
        
        DPRINTF(AnalysisFlag, "Agora: %lld\n", intersectionTable[i].dsaTime);
    }
    
    
    if(interseccao){
        interseccao = 0;
    }
    
    tempAnalisisWastedTicks = 0;
}


void Trace::ExeTracerRecord::descarteDeLoops()
{    
    loops[currentLoop].discarded = 1;
    loops[currentLoop].analyzed = 1;
    loops[currentLoop].vectorizable = 0;
    LoopAnalysis.enable = 0;
}


void Trace::ExeTracerRecord::verificaBranchs()
{
    if(instCond){
        branchOccurence = 1;
        
        if(LoopAnalysis.enable && instAddress != loops[currentLoop].lastAddress){
            descarteDeLoops();
            
            DPRINTF(AnalysisFlag, "Descartando loop %d (cond)\n", currentLoop);
        }
    }
    
    if(LoopAnalysis.enable && instBranchSubRoutine){
        descarteDeLoops();
        
        DPRINTF(AnalysisFlag, "Descartando loop %d (subrotina)\n", currentLoop);
    }
}


void Trace::ExeTracerRecord::salvaDadosCmps()
{
    VerificationCache.write();
    
    //Salva dados usados na comparacaoloop
    if(instCmp){
        LoopAnalysis.cmpsAddress = instAddress;
        
        //Comparacao com constante
        if(thereIsConstant){
            LoopAnalysis.cmpsOp1 = regContent[InstRegs.rs1];
            LoopAnalysis.cmpsOp2 = constante;
        }
        //Comparacao com registrador
        else{
            if(InstRegs.rs1 != 99 && InstRegs.rs2 != 99){
                if(regContent[InstRegs.rs1] < regContent[InstRegs.rs2]){
                    LoopAnalysis.cmpsOp1 = regContent[InstRegs.rs1];
                    LoopAnalysis.cmpsOp2 = regContent[InstRegs.rs2];
                }
                else{
                    LoopAnalysis.cmpsOp1 = regContent[InstRegs.rs2];
                    LoopAnalysis.cmpsOp2 = regContent[InstRegs.rs1];
                }
            }
        }
    }
    //Descarta dados apos sobrescricao
    else if(instSetFlag){
        LoopAnalysis.cmpsAddress = 0;
    }
}


void Trace::ExeTracerRecord::analiseDeDependencias()
{
    //Verifica se um registrador com conteudo de store foi sobreescrito
    if(loops[currentLoop].storeDataAddress!=0){
        VerificationCache.read();
        
        if(loops[currentLoop].storeRegister != 99 && (loops[currentLoop].storeRegister == InstRegs.rd1 || 
                                                      loops[currentLoop].storeRegister == InstRegs.rd2)){
            
            DPRINTF(AnalysisFlag, "Registrador com conteudo de store sobreescrito (r%d)\n", loops[currentLoop].storeRegister);
            
            loops[currentLoop].storeRegister = 99;
        }
    }
    if(loops[currentLoop].iterations == 1){
        VerificationCache.write();
        
        //Armazenamento dos enderecos de dados dos stores
        if(loops[currentLoop].storeDataAddress==0){
            if((instType=="MemWrite" && !instCond) && InstRegs.rs1 != 99 && InstRegs.rs2 != 99){
                loops[currentLoop].storeInstAddress = instAddress;
                loops[currentLoop].storeDataAddress = dataAddress;
                
                DPRINTF(AnalysisFlag, "Endereco armazenado: %#x\n", loops[currentLoop].storeDataAddress);
                
                // ANALISE DE REGISTRADOR
                if(instMicro)
                    loops[currentLoop].storeRegister = InstRegs.rs1;
                else
                    loops[currentLoop].storeRegister = InstRegs.rs2;
                
                DPRINTF(AnalysisFlag, "Registrador armazenado: %d\n", loops[currentLoop].storeRegister);
            }
        }
        
        if(instAddress == loops[currentLoop].firstAddress){
            loops[currentLoop].neonInst = 0;
            loops[currentLoop].condInst = 0;
            loops[currentLoop].totalInst = 0;
            loops[currentLoop].procExecTime = 0;
        }
        /*
        DPRINTF(AnalysisFlag, "instMicro:   %d\n", instMicro);
        DPRINTF(AnalysisFlag, "instCmp:     %d\n", instCmp);
        DPRINTF(AnalysisFlag, "instSetFlag: %d\n", instSetFlag);
        */
        
        if(!controlInst)
            loops[currentLoop].totalInst++;
        
        if(!instMicro && !instCmp && !instSetFlag && instruction[0]!='b'){
            int instSimdLatency=0;
            
            //Instrucoes de divisao ou raiz quadrada nao sao pipelinezaveis tambem tem latencia de espera
            if(instType=="IntDiv" || instType=="FloatDiv" || instType=="FloatSqrt"){
                for(i=0; i<12; i++){
                    if(instType==InstLatency[i].instType){
                        instSimdLatency = CLOCKPERIOD * InstLatency[i].simdLatency;
                        break;
                    }
                }
            }
            else{
                instSimdLatency = CLOCKPERIOD;
            }
            
            
            LoopAnalysis.iterationTimeSimd += instSimdLatency;
            
            loops[currentLoop].neonInst++;
            
            //DPRINTF(AnalysisFlag, "neon++\n");
            
            if(instCond)
                loops[currentLoop].condInst++;
        }
        else{
            loops[currentLoop].procExecTime += CLOCKPERIOD;
            
            //DPRINTF(AnalysisFlag, "proc++\n");
        }
    }
    else if(loops[currentLoop].iterations == 2){
        VerificationCache.read();
        
        //Verifica load de dado em endereco salvo na primeira iteracao
        if(instType=="MemRead" && !instCond){
            if(dataAddress == loops[currentLoop].storeDataAddress){
                loops[currentLoop].vectorizable = 0;
                
                DPRINTF(AnalysisFlag, "Load de dado em endereco salvo na primeira iteracao\n");
            }
        }
        //Verifica se um registrador com conteudo de store foi reutilizado
        if(!instCmp && loops[currentLoop].storeRegister != 99 &&
                      (loops[currentLoop].storeRegister == InstRegs.rs1 ||
                       loops[currentLoop].storeRegister == InstRegs.rs2 ||
                       loops[currentLoop].storeRegister == InstRegs.rs3 ||
                       loops[currentLoop].storeRegister == InstRegs.rs4)){
            loops[currentLoop].vectorizable = 0;
            
            DPRINTF(AnalysisFlag, "Registrador com conteudo de store reutilizado\n");
        }
        
        /*
        //Armazena o tamanho do dado salvo em bytes
        if((instType=="MemWrite" && !instCond) && instAddress == loops[currentLoop].storeInstAddress){
            loops[currentLoop].storeDataSize = dataAddress - loops[currentLoop].storeDataAddress;
            
            DPRINTF(AnalysisFlag, "Tamanho do dado em bytes %d\n", loops[currentLoop].storeDataSize);
        }
        */
        if(loops[currentLoop].storeDataSize < getSize()){
            loops[currentLoop].storeDataSize = getSize();
            
            DPRINTF(AnalysisFlag, "Tamanho do dado em bytes %d\n", loops[currentLoop].storeDataSize);
        }
    }
}


void Trace::ExeTracerRecord::inicializaVariaveisDeLatencia()
{
    if(inicialization){
        inicialization=0;
        
        InstLatency[0].instType="MemRead";
        InstLatency[0].simdLatency=1;
        InstLatency[0].cont=0;
        InstLatency[0].simdCont=0;
        InstLatency[1].instType="MemWrite";
        InstLatency[1].simdLatency=1;
        InstLatency[1].cont=0;
        InstLatency[1].simdCont=0;
        InstLatency[2].instType="IntAlu";
        InstLatency[2].simdLatency=4;
        InstLatency[2].cont=0;
        InstLatency[2].simdCont=0;
        InstLatency[3].instType="IntMult";
        InstLatency[3].simdLatency=5;
        InstLatency[3].cont=0;
        InstLatency[3].simdCont=0;
        InstLatency[4].instType="IntDiv";
        InstLatency[4].simdLatency=5;
        InstLatency[4].cont=0;
        InstLatency[4].simdCont=0;
        InstLatency[5].instType="FloatMemRead";
        InstLatency[5].simdLatency=1;
        InstLatency[5].cont=0;
        InstLatency[5].simdCont=0;
        InstLatency[6].instType="FloatMemWrite";
        InstLatency[6].simdLatency=1;
        InstLatency[6].cont=0;
        InstLatency[6].simdCont=0;
        InstLatency[7].instType="FloatAdd";
        InstLatency[7].simdLatency=5;
        InstLatency[7].cont=0;
        InstLatency[7].simdCont=0;
        InstLatency[8].instType="FloatCmp";
        InstLatency[8].simdLatency=3;
        InstLatency[8].cont=0;
        InstLatency[8].simdCont=0;
        InstLatency[9].instType="FloatMult";
        InstLatency[9].simdLatency=3;
        InstLatency[9].cont=0;
        InstLatency[9].simdCont=0;
        InstLatency[10].instType="FloatDiv";
        InstLatency[10].simdLatency=3;
        InstLatency[10].cont=0;
        InstLatency[10].simdCont=0;
        InstLatency[11].instType="FloatSqrt";
        InstLatency[11].simdLatency=9;
        InstLatency[11].cont=0;
        InstLatency[11].simdCont=0;
        
        for(i=0; i<12; i++){
            LoopTempLatency[i].instType = InstLatency[i].instType;
            LoopTempLatency[i].simdLatency = InstLatency[i].simdLatency;
            LoopTempLatency[i].cont = 0;
            LoopTempLatency[i].simdCont = 0;
        }
        
        LoopAnalysis.enable=0;
        
        //Zera vetor de estatisticas das configuracoes
        insereValorNoVetor(greatestTotalEconomiesDLP, nloops, 0, 0);
    }
}


void Trace::ExeTracerRecord::leituraDeParametros()
{
    int numint;
    string input, numstr="";
    ifstream arquivo;
    arquivo.open("/root/gem5/src/cpu/par.txt");

    if (arquivo.is_open()) {
        i=0;
    
        while (!arquivo.eof()) {
            arquivo >> input;
            
            //DPRINTF(ResultsFlag, "%s\n", input);
            
            std::istringstream convstrtoint(input);
            convstrtoint >> numint;
            
            switch(i){
                case 0:
                    NEONREGS = numint;
                    break;
            }
            
            i++;
        }
    }
    else{
        DPRINTF(ResultsFlag, "Arquivo de parametros par.txt nao encontrado\n");
        
        NEONREGS = 32;
    }
    arquivo.close();
    
    DPRINTF(ResultsFlag, "NEON 128-bit regs: %s\n\n", NEONREGS);
    
    DPRINTF(ResultsFlag, "MUTUALEXECUTION: %d\n", MUTUALEXECUTION);
    DPRINTF(ResultsFlag, "TABLEDECISION:   %d\n\n", TABLEDECISION);
    
    DPRINTF(ResultsFlag, "CACHESIZE (loops): %d\n", CACHESIZE);
    DPRINTF(ResultsFlag, "n (cgra configs):  %d\n\n", n);
    
    readPar = 0;
    
    return;
}


void Trace::ExeTracerRecord::leituraDeArquivo()
{
    bool delay=0, inicioTrace=0;
    long long int numint;
    string input, numstr="";
    ifstream arquivo;
    arquivo.open("/root/gem5/src/cpu/trace.txt");

    if (arquivo.is_open()) {
        i=0;
    
        while (!arquivo.eof()) {
            arquivo >> input;
            
            //DPRINTF(ResultsFlag, "%s\n", input);
            
            if(!inicioTrace){
                if(input == "SIMULATION")
                    delay=1;
                if(delay && input == "****")
                    inicioTrace=1;
            }
            else{
                std::istringstream convstrtoint(input);
                convstrtoint >> numint;
                
                // INSERIR BREAKS
                switch(i){
                    case 0:  currentTick = numint;      break;
                    case 1:  funct = input;             break;
                    case 2:  instAddress = numint;      break;
                    case 3:  instType = input;          break;
                    case 4:  instruction = input;       break;
                    case 5:  InstRegs.rd1 = numint;     break;
                    case 6:  InstRegs.rd2 = numint;     break;
                    case 7:  InstRegs.rs1 = numint;     break;
                    case 8:  InstRegs.rs2 = numint;     break;
                    case 9:  InstRegs.rs3 = numint;     break;
                    case 10: InstRegs.rs4 = numint;     break;
                    case 11: thereIsConstant = numint;  break;
                    case 12: constante = numint;        break;
                    case 13: dataAddress = numint;      break;
                    case 14: InstRegs.data = numint;    break;
                }
                
                i++;
                
                if(i==15){
                    i=0;
                    /*
                    DPRINTF(ResultsFlag, "currentTick     %ld\n", currentTick);
                    DPRINTF(ResultsFlag, "funct           %s\n", funct);
                    DPRINTF(ResultsFlag, "instAddress     %ld\n", instAddress);
                    DPRINTF(ResultsFlag, "instType        %s\n", instType);
                    DPRINTF(ResultsFlag, "instruction     %s\n", instruction);
                    DPRINTF(ResultsFlag, "InstRegs.rd1    %d\n", InstRegs.rd1);
                    DPRINTF(ResultsFlag, "InstRegs.rd2    %d\n", InstRegs.rd2);
                    DPRINTF(ResultsFlag, "InstRegs.rs1    %d\n", InstRegs.rs1);
                    DPRINTF(ResultsFlag, "InstRegs.rs2    %d\n", InstRegs.rs2);
                    DPRINTF(ResultsFlag, "InstRegs.rs3    %d\n", InstRegs.rs3);
                    DPRINTF(ResultsFlag, "InstRegs.rs4    %d\n", InstRegs.rs4);
                    DPRINTF(ResultsFlag, "thereIsConstant %d\n", thereIsConstant);
                    DPRINTF(ResultsFlag, "constante       %d\n", constante);
                    DPRINTF(ResultsFlag, "dataAddress     %ld\n", dataAddress);
                    DPRINTF(ResultsFlag, "InstRegs.data   %ld\n", InstRegs.data);
                    */
                    
                    
                    if(previousFunct[0]=='_' && previousFunct != funct){        
                        syscalltotals += currentTick-syscalltime;
                        
                        syscallOccurence = 0;
                        
                        //DPRINTF(ResultsFlag, "syscall fim\n");
                        //DPRINTF(ResultsFlag, " %ld - %ld = %ld\n", currentTick, syscalltime, currentTick-syscalltime);
                    }
                    if(funct[0]=='_' && previousFunct != funct){
                        syscalltime = currentTick;
                        
                        syscallOccurence = 1;
                        
                        //DPRINTF(ResultsFlag, "syscall inicio\n");
                    }
                    
                    previousFunct = funct;
                    
                    currentTick = currentTick-syscalltotals;
                    
                    if(!syscallOccurence)
                        exploracaoILP();
                }
            }
        }
    }
    else{
        printf("\nArquivo nao encontrado!\n\n");	
    }
    arquivo.close();
    
    DPRINTF(ResultsFlag, "syscall totals: %ld\n", syscalltotals);
    DPRINTF(ResultsFlag, "ECONOMIA ILP: %ld\n\n", economiaTotal);
    
    lido=1;
    syscallOccurence=0;
    printResults=0;
    
    return;
}


void Trace::ExeTracerRecord::analiseDeInterseccao(){
    if(!executaDLP && !executaILP)
        stateIntersection = 0;
    if( executaDLP && !executaILP)
        stateIntersection = 1;
    //if(interseccao &&  executaILP)
    if( executaDLP &&  executaILP)
        stateIntersection = 3;
    else if(!executaDLP &&  executaILP)
        stateIntersection = 2;
    /*
    if(interseccao &&  executaILP)
        stateIntersection = 3;
    */
    
    if(lastStateIntersection != stateIntersection){
        switch(lastStateIntersection){
            case 0:
                procTotalTicks += currentTick - stateChangeTick;
                break;
            
            case 1:
                dsaTotalTicks += currentTick - stateChangeTick;
                break;
            
            case 2:
                arrayTotalTicks += currentTick - stateChangeTick;
                break;
            
            case 3:
                bothTotalTicks += currentTick - stateChangeTick;
                break;
            
            default:
                DPRINTF(ResultsFlag, "\n\n DEU TRETA \n\n");
        }
        
        lastStateIntersection = stateIntersection;
        stateChangeTick = currentTick;
    }
}



void
ExeTracerRecord::dumpTicks(ostream &outs)
{
    ccprintf(outs, "%7d: ", when);
}

void Trace::ExeTracerRecord::imprimeTracePadrao(const StaticInstPtr &inst, bool ran){
    std::string sym_str;
    Addr sym_addr;
    Addr cur_pc = pc.instAddr();
    ostream &outs = Trace::output();
    
    if (!Debug::ExecUser || !Debug::ExecKernel) {
        bool in_user_mode = TheISA::inUserMode(thread);
        if (in_user_mode && !Debug::ExecUser) return;
        if (!in_user_mode && !Debug::ExecKernel) return;
    }
    
    if (Debug::ExecTicks)
        dumpTicks(outs);
    
    //outs << " isSyscall: " << inst->isSyscall() << " ";
    
    outs << thread->getCpuPtr()->name() << " ";

    if (Debug::ExecAsid)
        outs << "A" << dec << TheISA::getExecutingAsid(thread) << " ";

    if (Debug::ExecThread)
        outs << "T" << thread->threadId() << " : ";
        

    outs << pc.instAddr() << "\t";
    
    
    if (debugSymbolTable && Debug::ExecSymbol &&
            (!FullSystem || !inUserMode(thread)) &&
            debugSymbolTable->findNearestSymbol(cur_pc, sym_str, sym_addr)) {
        if (cur_pc != sym_addr)
            sym_str += csprintf("+%d", cur_pc - sym_addr);
        outs << "@" << sym_str;
    } 
    else {
        outs << "0x" << hex << cur_pc;
    }

    if (inst->isMicroop()) {
        outs << "." << setw(2) << dec << pc.microPC();
    } else {
        outs << "   ";
    }

    outs << " : ";

    //
    //  Print decoded instruction
    //

    outs << setw(26) << left;
    outs << inst->disassemble(cur_pc, debugSymbolTable);
    
    if (ran) {
        outs << " : ";

        if (Debug::ExecOpClass)
            outs << Enums::OpClassStrings[inst->opClass()] << " : ";

        if (Debug::ExecResult && !predicate)
            outs << "Predicated False";
        /* UPDATED
        if (Debug::ExecResult && data_status != DataInvalid) {
            switch (data_status) {
              case DataVec:
                {
                    ccprintf(outs, " D=0x[");
                    auto dv = data.as_vec->as<uint32_t>();
                    for (int i = TheISA::VecRegSizeBytes / 4 - 1; i >= 0;
                         i--) {
                        ccprintf(outs, "%08x", dv[i]);
                        if (i != 0) {
                            ccprintf(outs, "_");
                        }
                    }
                    ccprintf(outs, "]");
                }
                break;
              case DataVecPred:
                {
                    ccprintf(outs, " D=0b[");
                    auto pv = data.as_pred->as<uint8_t>();
                    for (int i = TheISA::VecPredRegSizeBits - 1; i >= 0; i--) {
                        ccprintf(outs, pv[i] ? "1" : "0");
                        if (i != 0 && i % 4 == 0) {
                            ccprintf(outs, "_");
                        }
                    }
                    ccprintf(outs, "]");
                }
                break;
              default:
                ccprintf(outs, " D=%#018x", data.as_int);
                break;
            }
        }
        */
        if (Debug::ExecResult && data_status != DataInvalid)
            ccprintf(outs, " D=%#018x", data.as_int);

        if (Debug::ExecEffAddr && getMemValid())
            outs << " A=0x" << hex << addr;
        
        if (Debug::ExecFetchSeq && fetch_seq_valid)
            outs << "  FetchSeq=" << dec << fetch_seq;

        if (Debug::ExecCPSeq && cp_seq_valid)
            outs << "  CPSeq=" << dec << cp_seq;

        if (Debug::ExecFlags) {
            outs << "  flags=(";
            inst->printFlags(outs, "|");
            outs << ")";
        }
    }

    
    //  End of line...
    
    outs << endl;
}


void Trace::ExeTracerRecord::imprimeTraceInjetorVHDL(const StaticInstPtr &inst, bool ran){
    std::string sym_str;
    Addr sym_addr;
    Addr cur_pc = pc.instAddr();
    ostream &outs = Trace::output();
    
    if (Debug::ExecTicks)
        dumpTicks(outs);
    
    outs << thread->getCpuPtr()->name() << " ";

    if (Debug::ExecAsid)
        outs << "A" << dec << TheISA::getExecutingAsid(thread) << " ";

    if (Debug::ExecThread)
        outs << "T" << thread->threadId() << " : ";
        

    outs << pc.instAddr() << "\t";
    
    
    if (debugSymbolTable && Debug::ExecSymbol &&
            (!FullSystem || !inUserMode(thread)) &&
            debugSymbolTable->findNearestSymbol(cur_pc, sym_str, sym_addr)) {
        if (cur_pc != sym_addr)
            sym_str += csprintf("+%d", cur_pc - sym_addr);
        outs << "@" << sym_str;
    } 
    else {
        outs << "0x" << hex << cur_pc;
    }


    outs << " : ";

    //
    //  Print decoded instruction
    //

    outs << setw(26) << left;
    outs << inst->disassemble(cur_pc, debugSymbolTable);
    
    if (ran) {/*
        outs << " : ";

        if (Debug::ExecOpClass)
            outs << Enums::OpClassStrings[inst->opClass()] << " : ";

        if (Debug::ExecResult && !predicate)
            outs << "Predicated False";
        */
        if (Debug::ExecResult && data_status != DataInvalid)
            ccprintf(outs, " D=%#018x", data.as_int);

        if (Debug::ExecEffAddr && getMemValid())
            outs << " A=0x" << hex << addr;
        /*
        if (Debug::ExecFetchSeq && fetch_seq_valid)
            outs << "  FetchSeq=" << dec << fetch_seq;

        if (Debug::ExecCPSeq && cp_seq_valid)
            outs << "  CPSeq=" << dec << cp_seq;

        if (Debug::ExecFlags) {
            outs << "  flags=(";
            inst->printFlags(outs, "|");
            outs << ")";
        }
        */
    }

    
    //  End of line...
    
    outs << endl;
}


void Trace::ExeTracerRecord::getReg(const StaticInstPtr &inst, long long int dado, bool dsa)
{
    int flagCount = 0;
    int index = 0;

    //Verificacao dos registradores fontes e destinos
    while(index < inst->numDestRegs()){ 
        if(inst->destRegIdx(index).isCCReg()){
            flagCount = flagCount + 1;
        }
        ///*
        else if((index-flagCount)==0){
            InstRegs.rd1 = inst->destRegIdx(index).index();
            
            if(InstRegs.rd1 >= 0 && InstRegs.rd1 < num_regs_proc)
                regContent[InstRegs.rd1] = dado;
            else
                regContent[num_regs_proc-1] = dado;
        }
        else if((index-flagCount)==1){
            InstRegs.rd2 = inst->destRegIdx(index).index();
            
            if(InstRegs.rd1 >= 0 && InstRegs.rd2 < num_regs_proc)
                regContent[InstRegs.rd2] = dado;
            else
                regContent[num_regs_proc-1] = dado;
        }
        else{ 
            //DPRINTF(AnalysisFlag, "REGISTRADOR IGNORADO");            
        }            
        index = index + 1; 
    }

    int flagCount2 = 0;
    index = 0;

    while(index < inst->numSrcRegs()){
        if(inst->srcRegIdx(index).isCCReg() || inst->srcRegIdx(index).isMiscReg()){
            flagCount2 = flagCount2 + 1;              
        }
        ///*
        else if((index-flagCount2)==0){
            InstRegs.rs1 = inst->srcRegIdx(index).index();
        }
        else if((index-flagCount2)==1){
            InstRegs.rs2 = inst->srcRegIdx(index).index();
        }
        else if((index-flagCount2)==2){
            InstRegs.rs3 = inst->srcRegIdx(index).index();
        }
        else if((index-flagCount2)==3){
            InstRegs.rs4 = inst->srcRegIdx(index).index();
        }
        else{
            //DPRINTF(AnalysisFlag, "REGISTRADOR IGNORADO");                
        }

        index = index + 1;
    }
    
    //DPRINTF(AnalysisFlag, "(%d) %d %d / %d %d - %d %d %d %d\n", inst->numSrcRegs(), flagCount, flagCount2, InstRegs.rd1, InstRegs.rd2, InstRegs.rs1, InstRegs.rs2, InstRegs.rs3, InstRegs.rs4);
}


long long int offset=0;

void Trace::ExeTracerRecord::extraiDadosDoTrace(const StaticInstPtr &inst, bool ran, bool traceArquivo)
{
    ostream &outs = Trace::output();
    std::string sym_str;
    Addr sym_addr;
    Addr cur_pc = pc.instAddr();
    
    previousFunct = funct;
    prevInst=instruction;
    prevInstType = instType;
    prevInstAddress = instAddress;
    
    PrevRegs = InstRegs;
    
    instAddress = pc.instAddr();
    
    //DPRINTF(ResultsFlag, "instAddress: %x\n", instAddress);
    
    previousFunct = funct;
    
    if (debugSymbolTable && Debug::ExecSymbol &&
            (!FullSystem || !inUserMode(thread)) &&
            debugSymbolTable->findNearestSymbol(cur_pc, sym_str, sym_addr)) {

        funct = sym_str;
        programCounter = cur_pc - sym_addr;
    }
    if (ran) {
        if (Debug::ExecOpClass)
            instType = Enums::OpClassStrings[inst->opClass()];
        if (Debug::ExecEffAddr && getMemValid())
            dataAddress = addr;
    }
    /*
    DPRINTF(ResultsFlag, "funct: %x\n", funct);
    DPRINTF(ResultsFlag, "programCounter: %d\n", programCounter);
    DPRINTF(ResultsFlag, "instType: %s\n", instType);
    DPRINTF(ResultsFlag, "dataAddress: %x\n", dataAddress);
    */
    //Contador do tipo de instrucao
    for(i=0; i<12; i++){
        if(instType==InstLatency[i].instType){
            if(executaDLP){
                LoopTempLatency[i].cont++;
            }
            else{
                InstLatency[i].cont++;
            }
            
            break;
        }
    }
    
    //Contagem dos tipos de instrucoes executadas (jordan)
    if(instType == "MemRead" || instType == "MemWrite"){
        totalMEM = totalMEM + 1;
    }
    else if(instType == "IntAlu"){
        totalALU = totalALU + 1;
    }
    else{
        totalOther = totalOther + 1;
    }
    
    //Contagem do numero total de instrucoes
    totalInst = totalInst + 1;
    
    
    if((previousFunct[0]=='_' && previousFunct[1]!='Z') && previousFunct != funct){
        syscalltotals += when-syscalltime;
        
        syscallOccurence = 0;
        
        //DPRINTF(ResultsFlag, "syscall fim\n");
        //DPRINTF(ResultsFlag, " %ld - %ld = %ld\n", when, syscalltime, when-syscalltime);
    }
    if((funct[0]=='_' && funct[1]!='Z') && previousFunct != funct){
        syscalltime = when;
        
        syscallOccurence = 1;
        
        //DPRINTF(ResultsFlag, "syscall inicio\n");
    }
    
    
    previousTick = currentTick;
    
    if(REMOVESYSCALLS)
        currentTick = when-syscalltotals;
    else
        currentTick = when;
    
    
    if(!traceArquivo){
        //Printa resultados
        if(funct == "_Exit" && printResults){
            printResults=0;
            
            outs << "\n";
            
            long long int economiaDSA = economiaDSAcount + economiaDSAsentinel + economiaDSAconditional + economiaDSAsentcond;
            //long long int discountedTicks = randomFunctTicks + printFunctTicks + (currentTick-inmainTicks);
            
            DPRINTF(ResultsFlag, "Ticks economizados pela CGRA(DLP):   %ld\t(%f %%)\n", economiaTotalDLP, (100*((float)economiaTotalDLP / (float)currentTick)));
            DPRINTF(ResultsFlag, "Ticks economizados pela CGRA(noDLP): %ld\t(%f %%)\n\n", (economiaTotal-economiaTotalDLP), (100*((float)(economiaTotal-economiaTotalDLP) / (float)currentTick)));
            DPRINTF(ResultsFlag, "Ticks economizados pela CGRA: %ld\t(%f %%)\n", economiaTotal, (100*((float)economiaTotal / (float)currentTick)));
            DPRINTF(ResultsFlag, "Ticks economizados pela DSA:  %ld\t(%f %%)\n\n", economiaDSA, (100*((float)economiaDSA / (float)currentTick)));
            
            DPRINTF(ResultsFlag, "Speedup da CGRA: %.3f x\n", (float)currentTick / ((float)currentTick - (float)economiaTotal));
            DPRINTF(ResultsFlag, "Speedup da DSA:  %.3f x\n\n", (float)currentTick / ((float)currentTick - (float)economiaDSA));
            
            
            arrayTotalTicks -= analisisWastedTicks;
                        
            DPRINTF(ResultsFlag, "Ticks executados no processador:    %ld\t(%f %%)\n", procTotalTicks, (100*((float)procTotalTicks / (float)currentTick)));
            DPRINTF(ResultsFlag, "Ticks executados na DSA:            %ld\t(%f %%)\n", dsaTotalTicks, (100*((float)dsaTotalTicks / (float)currentTick)));
            DPRINTF(ResultsFlag, "Ticks executados na CGRA:           %ld\t(%f %%)\n", arrayTotalTicks, (100*((float)arrayTotalTicks / (float)currentTick)));
            //DPRINTF(ResultsFlag, "Ticks executados na DSA e CGRA:     %ld\t(%f %%)\n\n", bothTotalTicks, (100*((float)bothTotalTicks / (float)currentTick)));
            
            DPRINTF(ResultsFlag, "Ticks de DLP executados na CGRA:    %ld\t(%f %%)\n", bothTotalTicks+analisisWastedTicks, (100*((float)(bothTotalTicks+analisisWastedTicks) / (float)currentTick)));
            DPRINTF(ResultsFlag, "Ticks exec CGRA em SentinelLoops:   %ld\t(%f %%)\n", bothTotalTicks, (100*((float)bothTotalTicks / (float)currentTick)));
            DPRINTF(ResultsFlag, "Ticks exec CGRA com DSA analisando: %ld\t(%f %%)\n\n", analisisWastedTicks, (100*((float)analisisWastedTicks / (float)currentTick)));
                        
            
            DPRINTF(ResultsFlag, "Total de interseccoes: %ld\n", lastInterIdx);
            DPRINTF(ResultsFlag, "DSA Wins:  %ld  (%.1f %%)\n", dsaWins, (100*dsaWinsPerc)/dsaWins);
            DPRINTF(ResultsFlag, "CGRA Wins: %ld  (%.1f %%)\n\n\n", arrayWins, (100*arrayWinsPerc)/arrayWins);
            DPRINTF(ResultsFlag, "DSA Avg Parallelism: %ld\n", (loopOnDSAAvgParallelism)/(arrayWins+dsaWins));
            DPRINTF(ResultsFlag, "CGRA Avg IPC:        %ld\n", (loopOnArrayAvgIPC)/(arrayWins+dsaWins));
            
            
            double energyDSA = (((float)detectionLatency / 1000000000000) * POWER_DSA) / 1000000000000;
            double energyDIM = (((float)currentTick / 1000000000000) * POWER_DIM) / 1000000000000;
            long long int CGRAticks = (arrayTotalTicks - economiaTotal);
            double energyCGRA = (((float)CGRAticks / 1000000000000) * POWER_CGRA) / 1000000000000;
                        
            DPRINTF(ResultsFlag, "Energia consumida pela DSA:  %.12f J\n", energyDSA);
            DPRINTF(ResultsFlag, "Energia consumida pelo BT:  %.12f J\n", energyDIM);
            DPRINTF(ResultsFlag, "Energia consumida pela CGRA: %.12f J\n", energyCGRA);
            DPRINTF(ResultsFlag, "Energia consumida BT+CGRA:  %.12f J\n\n\n", energyDIM + energyCGRA);
            
            /*
            outs << "Dados detalhados da Aplicacao:\n\n";
            
            DPRINTF(ResultsFlag, "Ticks em Syscalls:            %ld\n", syscalltotals);
            DPRINTF(ResultsFlag, "Ticks na producao de dados    %ld\n", randomFunctTicks);
            DPRINTF(ResultsFlag, "Ticks dentro da main          %ld\n", inmainTicks);
            DPRINTF(ResultsFlag, "Ticks imprimindo resultados   %ld\n", printFunctTicks);
            DPRINTF(ResultsFlag, "Ticks totais para descontar   %ld\n\n", discountedTicks);
            
            outs << "Dados detalhados da CGRA:\n\n";
            
            outs << "TICKS TOTAIS: " << currentTick << "\n";                       
            outs << "TICKS TOTAIS CONFIGURACOES: " << totalTick << "\n";            
            outs << "NUMERO DE CONFIGURACOES: " << totalConfigs << "\n";            
            outs << "NUMERO DE HITS: " << totalHits << "\n";  
            outs << "NUMERO DE INSTRUCOES: " << totalInst << "\n"; 
            outs << "NUMERO DE INSTRUCOES CONDICIONAIS: " << condinstCount << "\n"; 
            outs << "NUMERO DE ALU: " << totalALU << "\n"; 
            outs << "NUMERO DE MEM: " << totalMEM << "\n"; 
            outs << "NUMERO DE BRANCHES: " << totalCond << "\n"; 
            outs << "NUMERO DE OTHERS: " << totalOther << "\n";    
            outs << "MAIOR ECONOMIA INDIVIDUAL: " << greatIndividualEconomy << "\n";
            outs << "ECONOMIA TOTAL: " << economiaTotal << "\n\n\n";
            
            
            outs << "Dados detalhados da DSA:\n\n";
            
            DPRINTF(ResultsFlag, "CountLoops        Total: %li\n", loop_count);
            DPRINTF(ResultsFlag, "DynamicRangeLoops Total: %li\n", loop_dynamicrange);
            DPRINTF(ResultsFlag, "SentinelLoops     Total: %li\n", loop_sentinel);
            DPRINTF(ResultsFlag, "ConditionalLoops  Total: %li\n", loop_cond);
            DPRINTF(ResultsFlag, "DynamicCondLoops  Total: %li\n", loop_dynamiccond);
            DPRINTF(ResultsFlag, "SentCondLoops     Total: %li\n\n", loop_sentcond);
            
            DPRINTF(ResultsFlag, "CountLoops        Economia Total: %ld \t(em syscalls: %ld)\n", economiaDSAcount, economiaDSAcount_syscall);
            DPRINTF(ResultsFlag, "CountLoops        Percentual de Economia:    %f %%.\n\n", (100*((float)economiaDSAcount / (float)currentTick)));
            DPRINTF(ResultsFlag, "DynamicRangeLoops Economia Total: %ld \t(em syscalls: 0)\n", economiaDSAdynamicrange);
            DPRINTF(ResultsFlag, "DynamicRangeLoops Percentual de Economia:    %f %%.\n\n", (100*((float)economiaDSAdynamicrange / (float)currentTick)));
            DPRINTF(ResultsFlag, "SentinelLoops     Economia Total: %ld \t(em syscalls: %ld)\n", economiaDSAsentinel, economiaDSAsentinel_syscall);
            DPRINTF(ResultsFlag, "SentinelLoops     Percentual de Economia:    %f %%.\n\n", (100*((float)economiaDSAsentinel / (float)currentTick)));
            DPRINTF(ResultsFlag, "ConditionalLoops  Economia Total: %ld \t(em syscalls: %ld)\n", economiaDSAconditional, economiaDSAconditional_syscall);
            DPRINTF(ResultsFlag, "ConditionalLoops  Percentual de Economia:    %f %%.\n\n", (100*((float)economiaDSAconditional / (float)currentTick)));
            DPRINTF(ResultsFlag, "DynamicCondLoops  Economia Total: %ld \t(em syscalls: 0)\n", economiaDSAdynamiccond);
            DPRINTF(ResultsFlag, "DynamicCondLoops  Percentual de Economia:    %f %%.\n\n", (100*((float)economiaDSAdynamiccond / (float)currentTick)));
            DPRINTF(ResultsFlag, "SentCondLoops     Economia Total: %ld \t(em syscalls: %ld)\n", economiaDSAsentcond, economiaDSAsentcond_syscall);
            DPRINTF(ResultsFlag, "SentCondLoops     Percentual de Economia:    %f %%.\n\n\n", (100*((float)economiaDSAsentcond / (float)currentTick)));
            
            DPRINTF(ResultsFlag, "NonVectLoops      Percentual de Execucao:    %f %%.\n", (100*((float)ticks_sequential_nonvect / (float)currentTick)));
            DPRINTF(ResultsFlag, "CountLoops        Percentual de Execucao:    %f %%.\n", (100*((float)ticks_sequential_count / (float)currentTick)));
            DPRINTF(ResultsFlag, "DynamicRangeLoops Percentual de Execucao:    %f %%.\n", (100*((float)ticks_sequential_dynamicrange / (float)currentTick)));
            DPRINTF(ResultsFlag, "SentinelLoops     Percentual de Execucao:    %f %%.\n", (100*((float)ticks_sequential_sentinel / (float)currentTick)));
            DPRINTF(ResultsFlag, "ConditionalLoops  Percentual de Execucao:    %f %%.\n", (100*((float)ticks_sequential_conditional / (float)currentTick)));
            DPRINTF(ResultsFlag, "DynamicCondLoops  Percentual de Execucao:    %f %%.\n", (100*((float)ticks_sequential_dynamiccond / (float)currentTick)));
            DPRINTF(ResultsFlag, "SentCondLoops     Percentual de Execucao:    %f %%.\n\n\n", (100*((float)ticks_sequential_sentcond / (float)currentTick)));
            
            DPRINTF(ResultsFlag, "CountLoops        Ticks SIMD: %ld\n", ticks_parallel_count);
            DPRINTF(ResultsFlag, "CountLoops        Ticks SISD: %ld\n", ticks_sequential_count);
            DPRINTF(ResultsFlag, "CountLoops        Percentual SIMD/SISD:    %f %%.\n\n", (100*((float)ticks_parallel_count / (float)ticks_sequential_count)));
            DPRINTF(ResultsFlag, "DynamicRangeLoops Ticks SIMD: %ld\n", ticks_parallel_dynamicrange);
            DPRINTF(ResultsFlag, "DynamicRangeLoops Ticks SISD: %ld\n", ticks_sequential_dynamicrange);
            DPRINTF(ResultsFlag, "DynamicRangeLoops Percentual SIMD/SISD:    %f %%.\n\n", (100*((float)ticks_parallel_dynamicrange / (float)ticks_sequential_dynamicrange)));
            DPRINTF(ResultsFlag, "SentinelLoops     Ticks SIMD: %ld\n", ticks_parallel_sentinel);
            DPRINTF(ResultsFlag, "SentinelLoops     Ticks SISD: %ld\n", ticks_sequential_sentinel);
            DPRINTF(ResultsFlag, "SentinelLoops     Percentual SIMD/SISD:    %f %%.\n\n", (100*((float)ticks_parallel_sentinel / (float)ticks_sequential_sentinel)));
            DPRINTF(ResultsFlag, "ConditionalLoops  Ticks SIMD: %ld\n", ticks_parallel_conditional);
            DPRINTF(ResultsFlag, "ConditionalLoops  Ticks SISD: %ld\n", ticks_sequential_conditional);
            DPRINTF(ResultsFlag, "ConditionalLoops  Percentual SIMD/SISD:    %f %%.\n\n", (100*((float)ticks_parallel_conditional / (float)ticks_sequential_conditional)));
            DPRINTF(ResultsFlag, "DynamicCondLoops  Ticks SIMD: %ld\n", ticks_parallel_dynamiccond);
            DPRINTF(ResultsFlag, "DynamicCondLoops  Ticks SISD: %ld\n", ticks_sequential_dynamiccond);
            DPRINTF(ResultsFlag, "DynamicCondLoops  Percentual SIMD/SISD:    %f %%.\n\n", (100*((float)ticks_parallel_dynamiccond / (float)ticks_sequential_dynamiccond)));
            DPRINTF(ResultsFlag, "SentCondLoops     Ticks SIMD: %ld\n", ticks_parallel_sentcond);
            DPRINTF(ResultsFlag, "SentCondLoops     Ticks SISD: %ld\n", ticks_sequential_sentcond);
            DPRINTF(ResultsFlag, "SentCondLoops     Percentual SIMD/SISD:    %f %%.\n\n\n", (100*((float)ticks_parallel_sentcond / (float)ticks_sequential_sentcond)));
            */
            
            outs << "Dados de latencia:\n\n";
            
            DPRINTF(ResultsFlag, "BT Cache Access Delay:  %lli\n", BTCGRACache.calculateDelay());
            DPRINTF(ResultsFlag, "BT Cache Read/Writes %d/%d\n\n", BTCGRACache.getReads(), BTCGRACache.getWrites());
            
            DPRINTF(ResultsFlag, "DSA Cache Access Delay:  %lli\n", DSACache.calculateDelay());
            DPRINTF(ResultsFlag, "DSA Cache Read/Writes %d/%d\n", DSACache.getReads(), DSACache.getWrites());
            DPRINTF(ResultsFlag, "Verification Cache Access Delay:  %lli\n", VerificationCache.calculateDelay());
            DPRINTF(ResultsFlag, "Verification Cache Read/Writes:  %d/%d\n\n", VerificationCache.getReads(), VerificationCache.getWrites());
            
            DPRINTF(ResultsFlag, "History Table Access Delay:  %lli\n", HistoryTable.calculateDelay());
            DPRINTF(ResultsFlag, "History Table Read/Writes:  %d/%d\n\n", HistoryTable.getReads(), HistoryTable.getWrites());
            
            DPRINTF(ResultsFlag, "Detection Delay: %li\n", detectionLatency);
            DPRINTF(ResultsFlag, "Perc Detection Delay:   %f %%.\n\n", (100*((float)detectionLatency / (float)when)));
            
            /*
            outs << "Loops vetorizados:\n\n";
            
            for(i=0; i<CACHESIZE; i++){
                if(loops[i].vectorizable){
                    DPRINTF(ResultsFlag, "Loop nº %d\n", i);
                }
            }
            
            if(cacheFull)
                outs << "(cacheFull)\n\n";
            
            
            outs << "Instrucoes SISD e SIMD:\n\n";
            
            for(i=0; i<12; i++){
                DPRINTF(ResultsFlag, "%s: %li\n", InstLatency[i].instType, InstLatency[i].cont);
                DPRINTF(ResultsFlag, "Simd%s: %li\n\n", InstLatency[i].instType, InstLatency[i].simdCont);
            }
            
            outs << "inserir no arquivo stats.txt\n\n";
            
            for(i=0; i<12; i++){
                outs << "system.cpu.iq.FU_type_0::" << InstLatency[i].instType << " " << InstLatency[i].cont << "\n";
                
                if(i!=0 && i!=1 && i!=5 && i!=6){
                    outs << "system.cpu.iq.FU_type_0::Simd"; 
                    
                    if(i==2)
                        outs << "Alu";
                    else if(i==3)
                        outs << "Mult";
                    else if(i==4)
                        outs << "Misc";
                    else
                        outs << InstLatency[i].instType;
                    
                    outs << " " << InstLatency[i].simdCont << "\n";
                }
                
                if(i==0 || i==1){
                    InstLatency[i+5].cont += InstLatency[i].simdCont;
                }
            }
            
            outs << "\n\n\nConfigurações geradas pela DSA e pelo DIM\n\n";
            
            
            long long int mainEconomy = 0;
            
            for(i=0; i<nconfigs; i++){
                if(greatestTotalEconomiesILP[i].address != 0){
                //if(greatestTotalEconomiesILP[i].address != 0 && (100*((float)greatestTotalEconomiesILP[i].economy / (float)currentTick)) > 0.5){
                    DPRINTF(ResultsFlag, "Config %d\n", i);
                    DPRINTF(ResultsFlag, "Endereco: %lld\n", greatestTotalEconomiesILP[i].address);
                    DPRINTF(ResultsFlag, "Economia: %lld\t(%f %%)\n\n", greatestTotalEconomiesILP[i].economy, (100*((float)greatestTotalEconomiesILP[i].economy / (float)currentTick)));
                    
                    mainEconomy += greatestTotalEconomiesILP[i].economy;
                }
            }
            
            DPRINTF(ResultsFlag, "Economias: %lld\t(%f %%)\n\n", mainEconomy, (100*((float)mainEconomy / (float)currentTick)));
            
            mainEconomy=0;
            
            for(i=0; i<nloops; i++){
                if(greatestTotalEconomiesDLP[i].address != 0){
                //if(greatestTotalEconomiesDLP[i].address != 0 && (100*((float)greatestTotalEconomiesDLP[i].economy / (float)currentTick)) > 0.5){
                    DPRINTF(ResultsFlag, "Loop %d\n", i);
                    DPRINTF(ResultsFlag, "Endereco: %lld\n", greatestTotalEconomiesDLP[i].address);
                    DPRINTF(ResultsFlag, "Economia: %lld\t(%f %%)\n\n", greatestTotalEconomiesDLP[i].economy, (100*((float)greatestTotalEconomiesDLP[i].economy / (float)currentTick)));
                    
                    mainEconomy += greatestTotalEconomiesDLP[i].economy;
                }
            }
            
            DPRINTF(ResultsFlag, "Economias: %lld\t(%f %%)\n\n", mainEconomy, (100*((float)mainEconomy / (float)currentTick)));
            */
        }
    }
    
    InstRegs.data = data.as_int;
    InstRegs.rd1 = 99;
    InstRegs.rd2 = 99;
    InstRegs.rs1 = 99;
    InstRegs.rs2 = 99;
    InstRegs.rs3 = 99;
    InstRegs.rs4 = 99;

    //DPRINTF(ResultsFlag, "currentTick: %ld\n", currentTick);
    getReg(inst,data.as_int,1);
    

    //Extracao da instrucao da string
    string buf, word2, word3, word4, word5, word6, cons="";
    stringstream ss(inst->disassemble(cur_pc, debugSymbolTable));
    vector<string> tokens;
    
    fullInstruction = inst->disassemble(cur_pc, debugSymbolTable);

    i=1;

    //Separacao das palavras da string
    while (ss >> buf){
        if(i==1)
            instruction=buf;
        if(i==2)
            word2=buf;
        if(i==3)
            word3=buf;
        if(i==4)
            word4=buf;
        if(i==5)
            word5=buf;
        if(i==6)
            word6=buf;

        tokens.push_back(buf);
        i++;
    }
    
    /*
    DPRINTF(ResultsFlag, "instruction: %s\n", instruction);
    DPRINTF(ResultsFlag, "word2: %s\n", word2);
    DPRINTF(ResultsFlag, "word3: %s\n", word3);
    DPRINTF(ResultsFlag, "word4: %s\n", word4);
    DPRINTF(ResultsFlag, "word5: %s\n", word5);
    DPRINTF(ResultsFlag, "word6: %s\n", word6);
    */
    
    int instSize=0;

    //Verifica o tamanho da instrucao
    while(instruction[instSize]!='\0')
        instSize++;


    //DPRINTF(ResultsFlag, "instSize: %d\n", instSize);


    instBranchSubRoutine=0;
    instCond=0;
    instMicro=0;
    instCmp=0;
    instSetFlag=0;

    //Verifica saltos de subrotina
    if(instSize>=2 && instruction[0]=='b' && (instruction[1]=='l' || instruction[1]=='x')){
        instBranchSubRoutine=1;
        //DPRINTF(AnalysisFlag, "branchSubRoutine\n");
    }
    //Verifica instrucao de comparacao
    else if(instruction=="cmps")
        instCmp=1;
    //Verifica instrucoes que setam flags
    else if((instSize<=4) && (instruction[0]!='b') && (instruction[instSize-1]=='s') )
        instSetFlag=1;
    //Verifica instrucoes de condicionais
    else if((instSize>=3) && ((instruction[instSize-2]=='e' && instruction[instSize-1]=='q') ||
                              (instruction[instSize-2]=='n' && instruction[instSize-1]=='e') ||
                              (instruction[instSize-2]=='c' && instruction[instSize-1]=='s') ||
                              (instruction[instSize-2]=='c' && instruction[instSize-1]=='c') ||
                              (instruction[instSize-2]=='m' && instruction[instSize-1]=='i') ||
                              (instruction[instSize-2]=='p' && instruction[instSize-1]=='l') ||
                              (instruction[instSize-2]=='v' && instruction[instSize-1]=='s') ||
                              (instruction[instSize-2]=='v' && instruction[instSize-1]=='c') ||
                              (instruction[instSize-2]=='h' && instruction[instSize-1]=='i') ||
                              (instruction[instSize-2]=='l' && instruction[instSize-1]=='s') ||
                              (instruction[instSize-2]=='g' && instruction[instSize-1]=='e') ||
                              (instruction[instSize-2]=='l' && instruction[instSize-1]=='t') ||
                              (instruction[instSize-2]=='g' && instruction[instSize-1]=='t') ||
                              (instruction[instSize-2]=='l' && instruction[instSize-1]=='e'))){
        instCond=1;
        condinstCount = condinstCount + 1;
    }
    else if(instSize>=3 && instruction[instSize-4]=='_' && instruction[instSize-3]=='u'
                        && instruction[instSize-2]=='o' && instruction[instSize-1]=='p')
        instMicro=1;
    
    
    controlInst=0;
    
    if(inst->isControl())
        controlInst=1;


    thereIsConstant=0;

    //Extracao da constante da string
    if(instCmp){
        if(word2[0]=='#'){
            thereIsConstant=1;
            for (const auto c: word2){
                if(!ispunct(c))
                    cons.push_back(c);
            }
        }
        else if(word3[0]=='#'){
            thereIsConstant=1;
            for (const auto c: word3){
                if(!ispunct(c))
                    cons.push_back(c);
            }
        }
        else if(word4[0]=='#'){
            thereIsConstant=1;
            for (const auto c: word4){
                if(!ispunct(c))
                    cons.push_back(c);
            }
        }
        else if(word5[0]=='#'){
            thereIsConstant=1;
            for (const auto c: word5){
                if(!ispunct(c))
                    cons.push_back(c);
            }
        }
        else if(word6[0]=='#'){
            thereIsConstant=1;
            for (const auto c: word6){
                if(!ispunct(c))
                    cons.push_back(c);
            }
        }
        
        if(thereIsConstant){
            std::istringstream convstrtoint(cons);
            convstrtoint >> constante;
        }
    }
    
    
    
    if(ran && instType=="MemWrite"){
        if(word2[0]=='r'){
            string regconv="";
            i=0;
            
            do{
                word2[i] = word2[i+1];
                i++;
            }while(word2[i]!=',');
            
            for (const auto c: word2){
                if(!ispunct(c))
                    regconv.push_back(c);
            }
            
            std::istringstream convstrtoint(regconv);
            convstrtoint >> InstRegs.rs3;
        }
        else if(word2=="fp,"){
            InstRegs.rs3 = 11;
        }
        else if(word2=="sp,"){
            InstRegs.rs3 = 13;
        }
        else if(word2=="lr,"){
            InstRegs.rs3 = 14;
        }
        else if(word2=="pc,"){
            InstRegs.rs3 = 15;
        }
        
        /*
        imprimeTracePadrao(inst, ran);
        DPRINTF(AnalysisFlag, "%d %d  %d %d %d %d\n", InstRegs.rd1, InstRegs.rd2, InstRegs.rs1, InstRegs.rs2, InstRegs.rs3, InstRegs.rs4);
        */
    }
    
    
    /*
    DPRINTF(ResultsFlag, "instBranchSubRoutine: %d\n", instBranchSubRoutine);
    DPRINTF(ResultsFlag, "instCond: %d\n", instCond);
    DPRINTF(ResultsFlag, "instMicro: %d\n", instMicro);
    DPRINTF(ResultsFlag, "instCmp: %d\n", instCmp);
    DPRINTF(ResultsFlag, "instSetFlag: %d\n", instSetFlag);
    DPRINTF(ResultsFlag, "thereIsConstant: %d\n", thereIsConstant);
    if(thereIsConstant)
        DPRINTF(ResultsFlag, "constante: %d\n", constante);
    */
    
    
    
    if(ran && traceArquivo){
    /*
    if(ran && traceArquivo && funct=="main" && (instAddress >= 66688 && instAddress <= 66708)){
        
        if(instAddress==66688){
            offset+=24;
        }
        instAddress+=offset;
        */
        
        ccprintf(outs, "%d ", when);
        outs << funct << " ";
        outs << instAddress << " ";
        outs << instType << " ";    
        outs << instruction << " ";
        outs << InstRegs.rd1 << " ";
        outs << InstRegs.rd2 << " ";
        outs << InstRegs.rs1 << " ";
        outs << InstRegs.rs2 << " ";
        outs << InstRegs.rs3 << " ";
        outs << InstRegs.rs4 << " ";    
        outs << thereIsConstant << " ";
        outs << constante << " ";    
        outs << dataAddress << " ";
        outs << data.as_int << " ";
        
        outs << endl;
    }
}

void Trace::ExeTracerRecord::monitoraFuncoes(const StaticInstPtr &inst){
    Addr sym_addr;
    std::string sym_str, tempfunct, tempinst;
    stringstream ss(inst->disassemble(pc.instAddr(), debugSymbolTable));    
    ss >> tempinst;
    
    if (debugSymbolTable && Debug::ExecSymbol &&
            (!FullSystem || !inUserMode(thread)) &&
            debugSymbolTable->findNearestSymbol(pc.instAddr(), sym_str, sym_addr)) {

        tempfunct = sym_str;
    }
    
    
    if(tempfunct == "random")
        randomFunctTicks += when - prevWhen;
    
    
    //DPRINTF(ResultsFlag, "instruction: %s\n", tempinst);
    
    if(tempinst == "ldmstm"){
        if(tempfunct == "main"){
            //DPRINTF(ResultsFlag, "INICIO/FIM da main\n");
            
            if(inmainTicks == 0)
                inmainTicks = when;
            else
                inmainTicks = when - inmainTicks;
        }
        
        if(tempfunct == "___printf_chk"){
            //DPRINTF(ResultsFlag, "INICIO/FIM do print\n");
            
            if(tempDif == 0)
                tempDif = when;
            else{
                printFunctTicks += when - tempDif - tempDifAcc;
                tempDif = 0;
                tempDifAcc = 0;
            }
        }
    }
    
    if(tempDif != 0 && stateIntersection != 0){
        tempDifAcc += when - prevWhen;
    }
    
    prevWhen = when;
}

void printaArray(int index){
    ostream &outs = Trace::output();

    int aux2=0;
    for(i=0;i<line_number;i++){
        aux2 = 0;
        for(j=0;j<column_number;j++){
            if(j==0){
                if(i<mem_line)
                    outs << " ALU:" << "\t|\t";
                else if(i<mult_line)
                    outs << " MEM:" << "\t|\t";
                else if(i<float_line)
                    outs << " MUL:" << "\t|\t";
                else
                    outs << " FLO:" << "\t|\t";
            }
            
            if(aux2 == 3){
                outs << "|";
                outs << "\t";
                aux2 = 0;
            }
            aux2 = aux2 + 1;
            
            if(memoriaConfig[index].arrayMatrix[i][j] == 88)
                outs << "W\t";
            else if(memoriaConfig[index].arrayMatrix[i][j] != 99)
                ccprintf(outs, "%d\t", memoriaConfig[index].arrayMatrix[i][j]);
            else
                outs << "-\t";
       }
       outs << "\n";
    }
    outs << "\n";
}

void Trace::ExeTracerRecord::exploracaoILP(){
    int i, j, k, colunasArr = 0;
    
    // ANALISE INTERESECCAO
    // Verifica se array ainda esta em execucao
    if(executaILP){
        //if(instAddress < memoriaConfig[currentConfig].afterbranchId || instAddress > memoriaConfig[currentConfig].lastInstId){
        if(prevInstAddress == memoriaConfig[currentConfig].lastInstId){
        //if(instAddress == memoriaConfig[currentConfig].lastInstId){
            executaILP = 0;
            DPRINTF(AnalysisFlag, "executaILP = 0\n");
            
            
            if((currentTick - memoriaConfig[index_hit].lastHitTick) > 10000000 || memoriaConfig[index_hit].lastHitTick == 0)
                DPRINTF(ResultsFlag, "calculo do tempo enlouqueceu\n");
            
            
            //int tempEconomy = difTick - (oneConfigCycles*CLOCKPERIOD + CACHE_HIT_DELAY*CLOCKPERIOD);
            long long int arrayExecTime = memoriaConfig[currentConfig].configCycles*CLOCKPERIOD + CACHE_HIT_DELAY*CLOCKPERIOD;
            long long int procExecTime = currentTick - memoriaConfig[currentConfig].lastHitTick;
            long long int tempEconomy = procExecTime - arrayExecTime;
            
            DPRINTF(AnalysisFlag, "prevInstAddress:   %lld\n", prevInstAddress);
            DPRINTF(AnalysisFlag, "currentTick:   %lld\n", currentTick);
            DPRINTF(AnalysisFlag, "lastHitTick:   %lld\n\n", memoriaConfig[currentConfig].lastHitTick);
            DPRINTF(AnalysisFlag, "Arraytime:   %lld\n", arrayExecTime);
            DPRINTF(AnalysisFlag, "Proctime:    %lld\n", procExecTime);
            DPRINTF(AnalysisFlag, "tempEconomy: %lld\n\n", tempEconomy);
            
            if(tempEconomy > procExecTime){
                DPRINTF(ResultsFlag, "Economia maior que proctime\n");
                DPRINTF(ResultsFlag, "Arraytime:   %lld\n", arrayExecTime);
                DPRINTF(ResultsFlag, "Proctime:    %lld\n", procExecTime);
                DPRINTF(ResultsFlag, "tempEconomy: %lld\n\n", tempEconomy);
                
                tempEconomy = 0;
            }

            if(greatIndividualEconomy < tempEconomy){
                greatIndividualEconomy = tempEconomy;
            }

            int notSavedConfig = 0;

            if(tempEconomy < 0){
                notSavedConfig = 1;
                
                //outs << "\n"; 
                DPRINTF(AnalysisFlag, "\n");
            }
            
            if(notSavedConfig == 0){
                //executaILP=1;
                //DPRINTF(AnalysisFlag, "executaILP = 1\n");
                
                economiaTotal += tempEconomy;
                
                if(stateIntersection == 3)
                    economiaTotalDLP += tempEconomy;
                
                if(memoriaConfig[currentConfig].afterbranchId != 0)
                    insereValorNoVetor(greatestTotalEconomiesILP, nconfigs, memoriaConfig[currentConfig].afterbranchId, tempEconomy);
                else
                    DPRINTF(ResultsFlag, "Endereco 0 at the address: %lld (economy: %lld)\n", memoriaConfig[currentConfig].lastInstId, tempEconomy);
                
                
                /*
                double fuEnergy, fuPower=0;
                
                for(i=0;i<line_number;i++){
                    //for(j=0;j<column_number;j++){
                    for(j=0;j<column_number;j+=3){
                        //if(memoriaConfig[index_hit].arrayMatrix[i][j] != 99){
                        if(memoriaConfig[index_hit].arrayMatrix[i][j] != 99 ||
                           memoriaConfig[index_hit].arrayMatrix[i][j+1] != 99 ||
                           memoriaConfig[index_hit].arrayMatrix[i][j+2] != 99){
                            if(i<2){
                                fuPower += POWER_INTALU;
                            }
                            else if(i<6){
                                fuPower += POWER_MEMACC;
                            }
                            else{
                                fuPower += POWER_INTMUL;
                            }
                        }
                    }
                }
                
                //pJ = pW*s
                fuEnergy = fuPower / (1000000000000 / CLOCKPERIOD);  // normalizacao para um periodo de clock (seg)
                fuEnergy *= 3;                              //3 ciclos de clock por nível
                
                DPRINTF(AnalysisFlag, "Energia consumida: %f pJ\n", fuEnergy);
                
                //totalEnergyCGRA += fuEnergy;
                */
            }
            
            
            //outs << "ECONOMIA TOTAL:  " << economiaTotal << "\n";
            DPRINTF(AnalysisFlag, "ECONOMIA TOTAL: %ld\n", economiaTotal);
            
            
        }
        else if(instAddress < memoriaConfig[currentConfig].afterbranchId || instAddress > memoriaConfig[currentConfig].lastInstId){
            DPRINTF(ResultsFlag, "caiu fora da configuracao\n");
        }
    }
    
    //Primeira alocacao, inicializando variaveis globais

    if(firsttime == 0){
        for(i=0;i<n;i++){
            memoriaConfig[i].afterbranchId = 0;
            memoriaConfig[i].lastID = 0;
            memoriaConfig[i].accesses = 0;
            memoriaConfig[i].inTick = 0;
            memoriaConfig[i].finTick = 0;
            memoriaConfig[i].configCycles = 0;
            memoriaConfig[i].specDeep = 0;
            
            memoriaConfig[i].lastInstId = 0;
            memoriaConfig[i].continues = 0;
            memoriaConfig[i].lastAllocatedColumn = 0;

            for(j=0;j<num_regs_proc;j++){
                memoriaConfig[i].readReg[j] = 0;
                memoriaConfig[i].writeReg[j] = 0;
            }

            for(j=0;j<line_number;j++){
                for(k=0;k<column_number;k++){
                    memoriaConfig[i].arrayMatrix[j][k] = 0; 
               }
            }
        }


        firsttime = 1;

        //LOGICA DE CONTEUDO DOS REGISTRADORES

        for(i=0;i<num_regs_proc;i++){
           specregWrite[i] = 0;
           specregRead[i] = 0;

           arrMap.registersMap[i] = 99;
           regRead[i] = 0;
           regWrite[i] = 0;
        }

        for(i=0;i<line_number;i++){
           for(j=0;j<column_number;j++){
             arrMap.arrayMatrix[i][j] = 99;
           }
        }
        
        
        for(i=0;i<64;i++){
            intersectionTable[i].address = 0;
        }
        
        //Zera vetor de estatisticas das configuracoes
        insereValorNoVetor(greatestTotalEconomiesILP, nconfigs, 0, 0);
    }

    //Verifica se uma instrucao e do tipo branch
    if(instruction[0] == 'b'){
        totalCond = totalCond + 1;
        branchInstruction = 1;
    }
    else{
        branchInstruction = 0;
    }
    

    if(previousWasBranch == 1 || (continues == 1 && executaILP == 0)){
        BTCGRACache.read();
        
        for(index_hit=0; index_hit<n; index_hit++){
            if(instAddress == memoriaConfig[index_hit].afterbranchId){
                 configurationHit = 1;
                 continues = 0;
                 break;
            }
        }
    }
    
    
    //Gerando Configuracao
    if(previousWasBranch == 1 && configStart == 0 && branchInstruction == 0 && configurationHit == 0){
        BTCGRACache.miss();
        
        configStart = 1;
        arrMap.afterbranchId = instAddress;
        
        //outs << "previousWasBranch = 1 configStart = 0 branchInstruction = 0 configurationHit = 0" << "\n";
        DPRINTF(AnalysisFlag, "previousWasBranch = 1 configStart = 0 branchInstruction = 0 configurationHit = 0\n");
        //outs << " ENTROU AQUI. Configuration ID:" << instAddress << "\n";
        DPRINTF(AnalysisFlag, "ENTROU AQUI. Configuration ID: %x\n", instAddress);
    }
    
    if(configStart == 1 && (branchInstruction == 1 || (controlInst == 1))){
        endArray = 1;
        
        if(controlInst)
            DPRINTF(AnalysisFlag, "endArray controlInst\n");
        
        /*
        if(previousFunct != funct && previousWasBranch == 0){
            configStart = 0;
            
            DPRINTF(AnalysisFlag, "configStart = 1 && (previousFunct != funct && previousWasBranch == 0)\n");
        }
        else{
            DPRINTF(AnalysisFlag, "configStart = 1 && branchInstruction = 1\n");
        }
        */
    }

    if(arrayFull == 1){
        arrayFull = 0;
        
        arrMap.afterbranchId = instAddress;
        
        //outs << "Continue: Configuration ID:" << "\n";
        DPRINTF(AnalysisFlag, "Continue: Configuration ID: %d\n", arrMap.afterbranchId);
    }

    if(branchInstruction == 1){
        previousWasBranch = 1;
        
        //outs << "previousWasBranch" << "\n";
        DPRINTF(AnalysisFlag, "previousWasBranch\n");
    }

    if(branchInstruction == 0){
        previousWasBranch = 0;
    }



    //DPRINTF(AnalysisFlag, "DEBUG: configStart -> %d\n", configStart);



    //Contagem de Ciclos

    decreaseCycle = 0;
    oneConfigCycles = 0;

    
    
    
    if(MUTUALEXECUTION && configurationHit == 1 && executaDLP == 1){
        if(TABLEDECISION){
            //Logica de decisao de engine (tabela)
            bool encontrado=0;
            
            HistoryTable.read();
            
            for(i=0; i<64; i++){
                if(loops[currentLoop].firstAddress == intersectionTable[i].address){
                    encontrado=1;
                    break;
                }
            }
            if(!encontrado){
                intersectionTable[lastInterIdx].address = loops[currentLoop].firstAddress;
                intersectionTable[lastInterIdx].dsaTime = loops[currentLoop].iterationTimeSimd / (16 / loops[currentLoop].storeDataSize);
                
                intersectionTable[lastInterIdx].arrayTime = 0;
                
                //Considera todas as configuracoes dentro do range do loop
                for(i=0; i<n; i++){
                    if(memoriaConfig[i].afterbranchId >= loops[currentLoop].firstAddress &&
                       memoriaConfig[i].lastInstId    <= loops[currentLoop].lastAddress)
                    intersectionTable[lastInterIdx].arrayTime += memoriaConfig[i].configCycles * CLOCKPERIOD;   
                }
                
                i = lastInterIdx;
                
                lastInterIdx = (lastInterIdx + 1) % 64;
                
                HistoryTable.write();
            }
            
            
            
            //configurationHit = 0;                                                     //NO ARRAY EXECUTION ON MUTUAL REGIONS
            
            if(!loops[currentLoop].definedSize && loops[currentLoop].executions == 0){
                arrayWins++;
                arrayWinsPerc += (float)intersectionTable[i].arrayTime / (float)intersectionTable[i].dsaTime;
                
                executaDLP = 0;
                
                interseccao = 1;
                
                //DPRINTF(ResultsFlag, "Sentinel stall at the address: %lld\n", intersectionTable[i].address);
            }
            else{
                if(intersectionTable[i].arrayTime < intersectionTable[i].dsaTime){    //ORIGINAL1
                //if(intersectionTable[i].arrayTime > intersectionTable[i].dsaTime){    //DECOUPLED
                    arrayWins++;
                    arrayWinsPerc += (float)intersectionTable[i].arrayTime / (float)intersectionTable[i].dsaTime;
                    
                    executaDLP = 0;
                    
                    DSACache.writeRevoked();
                    
                    DPRINTF(AnalysisFlag, "Array Wins:\n");
                }
                else{
                    dsaWins++;
                    dsaWinsPerc += (float)intersectionTable[i].dsaTime / (float)intersectionTable[i].arrayTime;
                    
                    DPRINTF(AnalysisFlag, "DSA Wins:\n");
                    
                    //DPRINTF(ResultsFlag, "DSA Wins at address: %lld\n", intersectionTable[i].address);
                    
                    configurationHit = 0;
                    
                    if(tempAnalisisWastedTicks != 0)
                        analisisWastedTicks += currentTick - tempAnalisisWastedTicks;
                }
                
                
                
                DPRINTF(AnalysisFlag, "%ld x %ld\n", intersectionTable[i].dsaTime, intersectionTable[i].arrayTime);
                
                if(intersectionTable[i].dsaTime >= 2*intersectionTable[i].arrayTime ||
                   intersectionTable[i].arrayTime >= 8*intersectionTable[i].dsaTime){                
                    DPRINTF(AnalysisFlag, "suspeito: %lld (%ld x %ld)\n", intersectionTable[i].address, intersectionTable[i].dsaTime, intersectionTable[i].arrayTime);
                }
            }
            
            tempAnalisisWastedTicks = 0;
        }
        else{
            //Logica de decisao de engine (OPC)
            long long int loopOnArrayCycles=0; //, loopOnArrayInst=0;
            float loopOnArrayIPC, loopOnDSAParallelism = (16 / loops[currentLoop].storeDataSize);
            
            for(i=0; i<n; i++){
                if(memoriaConfig[i].afterbranchId >= loops[currentLoop].firstAddress &&
                   memoriaConfig[i].lastInstId    <= loops[currentLoop].lastAddress){
                    loopOnArrayCycles += memoriaConfig[i].lastAllocatedColumn;
                    
                    
                    //DPRINTF(ResultsFlag, "memoriaConfig[%d].lastAllocatedColumn: %d\n", i, memoriaConfig[i].lastAllocatedColumn);
                    //printaArray(i);
                }
            }
            
            // 1 processor cycle == 3 cgra cycles
            loopOnArrayIPC = 3*(float)loops[currentLoop].neonInst / (float)loopOnArrayCycles;
            
            loopOnArrayAvgIPC += loopOnArrayIPC;
            loopOnDSAAvgParallelism += loopOnDSAParallelism;
            
            //DPRINTF(ResultsFlag, "loops[currentLoop].neonInst: %d\n", loops[currentLoop].neonInst);
            //DPRINTF(ResultsFlag, "loopOnArrayCycles: %ld\n", loopOnArrayCycles);
            //DPRINTF(ResultsFlag, "loopOnArrayIPC: %f\n", loopOnArrayIPC);
            
            if(loopOnArrayIPC >= loopOnDSAParallelism){
                arrayWins++;
                arrayWinsPerc += loopOnArrayIPC / loopOnDSAParallelism;
                
                executaDLP = 0;
                
                interseccao = 1;
                
                DSACache.writeRevoked();
                
                DPRINTF(AnalysisFlag, "Array Wins:\n");
            }
            else{
                dsaWins++;
                dsaWinsPerc += loopOnDSAParallelism / loopOnArrayIPC;
                
                configurationHit = 0;
                
                if(tempAnalisisWastedTicks != 0)
                    analisisWastedTicks += currentTick - tempAnalisisWastedTicks;
                
                DSACache.writeRevoked();
                
                DPRINTF(AnalysisFlag, "DSA Wins:\n");
            }
            
            //if(loopOnArrayIPC != 1)
            DPRINTF(AnalysisFlag, "%f x %f\n", loopOnArrayIPC, loopOnDSAParallelism);
            
            HistoryTable.read();
        }
    }
    
    if(configurationHit == 1 && (!MUTUALEXECUTION || executaDLP == 0)){
        configurationHit = 0;
        
        executaILP = 1;
        currentConfig = index_hit;
        memoriaConfig[index_hit].lastHitTick = currentTick;
       
        //outs << "INDEX HIT:  " << index_hit << "\n";
        DPRINTF(AnalysisFlag, "INDEX HIT:  %d\n", index_hit);

        memoriaConfig[index_hit].accesses = memoriaConfig[index_hit].accesses + 1;

        DPRINTF(AnalysisFlag, "HIT NO ID: %lld\n", memoriaConfig[index_hit].afterbranchId);
        
        DPRINTF(AnalysisFlag, "lastInstId: %lld\n", memoriaConfig[index_hit].lastInstId);
        
        DPRINTF(AnalysisFlag, "NUMERO DE ACESSOS: %lld\n", memoriaConfig[index_hit].accesses);

        //outs << currentTick << "HIT NA CACHE DE CONFIGURACAO\n";
        DPRINTF(AnalysisFlag, "HIT NA CACHE DE CONFIGURACAO\n");

        totalHits = totalHits + 1;
        DPRINTF(AnalysisFlag, "Total de Ciclos Hits Configuracao: %d\n", totalCycles);

        auxinTick = memoriaConfig[index_hit].inTick;
        auxfinTick = memoriaConfig[index_hit].finTick;

        //outs << "ID:  " << memoriaConfig[index_hit].afterbranchId << "\n";
        DPRINTF(AnalysisFlag, "ID:  %x\n", memoriaConfig[index_hit].afterbranchId);

        totalCycles = totalCycles + memoriaConfig[index_hit].configCycles;

        oneConfigCycles = memoriaConfig[index_hit].configCycles;

        if(memoriaConfig[index_hit].specDeep == 2){
            //outs << "  SpecVerification Begins  " << "\n";
            DPRINTF(AnalysisFlag, "  SpecVerification Begins  \n");
            
            lastID = memoriaConfig[index_hit].afterbranchId;
            for(i=0;i<num_regs_proc;i++){
                specregWrite[i] = memoriaConfig[index_hit].writeReg;
                specregRead[i] = memoriaConfig[index_hit].readReg;
            }
        }

        if(memoriaConfig[index_hit].specDeep == 1 && memoriaConfig[index_hit].lastID == lastID){

            lastID = memoriaConfig[index_hit].afterbranchId;

            //outs << "  SpecVerification Continue  " << "\n";
            DPRINTF(AnalysisFlag, "  SpecVerification Continue  \n");

            for(i=0;i<num_regs_proc;i++){

                if(specregRead[i] == memoriaConfig[index_hit].readReg[i]){

                    specregRead[i] = memoriaConfig[index_hit].readReg[i];
                    if(memoriaConfig[index_hit].readReg[i] == 1){
                        decreaseCycle = decreaseCycle + 1;    
                    }                                    
                } 
                else{
                    specregRead[i] = 1;
                }

                if(specregWrite[i] == memoriaConfig[index_hit].writeReg[i]){

                    specregWrite[i] = memoriaConfig[index_hit].writeReg[i];

                    if(memoriaConfig[index_hit].writeReg[i] == 1){
                        decreaseCycle = decreaseCycle + 1;    
                    }                                 
                } 
                else{
                    specregWrite[i] = 1;
                }
            }

        }
        
        //outs << "Decreased Cycles:   " << decreaseCycle << "\n"; 
        DPRINTF(AnalysisFlag, "Decreased Cycles:   %d\n", decreaseCycle);
         
        if(decreaseCycle%reg_per_cycle == 0){
            decreaseCycle = decreaseCycle/reg_per_cycle;
        }
        else{
            decreaseCycle = (decreaseCycle/reg_per_cycle) + 1;
        }

        totalCycles = totalCycles - decreaseCycle;

        //outs << "Before Decreased Cycles:   " << oneConfigCycles << "\n"; 
        DPRINTF(AnalysisFlag, "Before Decreased Cycles:   %d\n", oneConfigCycles);

        oneConfigCycles = oneConfigCycles - decreaseCycle;
        
        
        /*
        memoriaConfig[index_hit].configRealCycles = oneConfigCycles - decreaseCycle;
        memoriaConfig[index_hit].inTick = currentTick;
        */
        
        /*
        difTick = auxfinTick - auxinTick;

        totalTick = difTick + totalTick;

        //outs << "After Decreased Cycles:   " << oneConfigCycles << "\n"; 
        DPRINTF(AnalysisFlag, "After Decreased Cycles:   %d\n", oneConfigCycles);

        DPRINTF(AnalysisFlag, "Ticks Totais no Processador: %d\n", difTick);
        DPRINTF(AnalysisFlag, "Ticks Totais no Array: %d\n", (oneConfigCycles*CLOCKPERIOD + CACHE_HIT_DELAY*CLOCKPERIOD));

        long long int tempEconomy = difTick - (oneConfigCycles*CLOCKPERIOD + CACHE_HIT_DELAY*CLOCKPERIOD);
        
        if(tempEconomy > difTick){
            DPRINTF(ResultsFlag, "Economia maior que proctime\n");
            DPRINTF(ResultsFlag, "Arraytime:   %lld\n", (oneConfigCycles*CLOCKPERIOD + CACHE_HIT_DELAY*CLOCKPERIOD));
            DPRINTF(ResultsFlag, "Proctime:    %lld\n", difTick);
            DPRINTF(ResultsFlag, "tempEconomy: %lld\n\n", tempEconomy);
            
            tempEconomy = 0;
        }

        if(greatIndividualEconomy < tempEconomy){
            greatIndividualEconomy = tempEconomy;
        }

        int notSavedConfig = 0;

        if(tempEconomy < 0){
            notSavedConfig = 1;
            
            //outs << "\n"; 
            DPRINTF(AnalysisFlag, "\n");
        }
        
        if(notSavedConfig == 0){
            executaILP=1;
            DPRINTF(AnalysisFlag, "executaILP = 1\n");
            
            economiaTotal = economiaTotal + tempEconomy;
            
            currentConfig = index_hit;
            memoriaConfig[index_hit].lastHitTick = currentTick;
                        
            //
            double fuEnergy=0;
            
            for(i=0;i<line_number;i++){
                for(j=0;j<column_number;j++){                    
                    if(memoriaConfig[index_hit].arrayMatrix[i][j] != 99){
                        if(i<2){
                            fuEnergy += POWER_INTALU;
                        }
                        else if(i<6){
                            fuEnergy += POWER_MEMACC;
                        }
                        else{
                            fuEnergy += POWER_INTMUL;
                        }
                    }
                }
            }
            
            fuEnergy /= (3 * (1000000000000 / CLOCKPERIOD));  // um terco do periodo de clock
            
            DPRINTF(AnalysisFlag, "Energia consumida: %f pJ\n", fuEnergy);
            
            totalEnergyCGRA += fuEnergy;
            //
        }
        else{
             economiaTotal = economiaTotal;
        }
        
        
        //outs << "ECONOMIA TOTAL:  " << economiaTotal << "\n";
        DPRINTF(AnalysisFlag, "ECONOMIA TOTAL: %ld\n", economiaTotal);        
        
        tempEconomy = 0;
        */
        
        if(memoriaConfig[index_hit].continues == 1){
            continues = 1;
        }
        
        
        //printaArray(index_hit);

        DPRINTF(AnalysisFlag, "ID:  %x\n", memoriaConfig[index_hit].afterbranchId);
        DPRINTF(AnalysisFlag, "Last ID:  %x\n", memoriaConfig[index_hit].lastID);
        DPRINTF(AnalysisFlag, "ConfigCycles:  %d\n", memoriaConfig[index_hit].configCycles);
        DPRINTF(AnalysisFlag, "SpecDeep:  %d\n", memoriaConfig[index_hit].specDeep);
    }

    //DPRINTF(AnalysisFlag, "ECONOMIA TOTAL: %d\n", economiaTotal);
    //DPRINTF(AnalysisFlag, "TOTAL TICK: %d\n", totalTick);

    //DPRINTF(AnalysisFlag, "Tipo de Instrucao: %s\n", Enums::OpClassStrings[inst->opClass()]);

    if(configStart == 1){
        DPRINTF(AnalysisFlag, "configStart == 1\n");
        
        if(initArray == 0){
            //outs << "INICIO DE UMA CONFIGURACAO:    " << currentTick << "\n";
            DPRINTF(AnalysisFlag, "INICIO DE UMA CONFIGURACAO:    %d\n", currentTick);
            
            init_conf = 1;
            inTick = currentTick;
            //inTick = previousTick;
        }

        initArray = 1;
        
        if(InstRegs.rd1 != 99)  regWrite[InstRegs.rd1] = 1;
        if(InstRegs.rd2 != 99)  regWrite[InstRegs.rd2] = 1;
        if(InstRegs.rs1 != 99)  regRead[InstRegs.rs1]  = 1;
        if(InstRegs.rs2 != 99)  regRead[InstRegs.rs2]  = 1;
        if(InstRegs.rs3 != 99)  regRead[InstRegs.rs3]  = 1;
        if(InstRegs.rs4 != 99)  regRead[InstRegs.rs4]  = 1;
        
        
        int allocate = 0;
        
        if(instType == "IntAlu"){
            DPRINTF(AnalysisFlag, "Acesso a ALU\n");
            int x = 0; // aux1 = 3, memdep = 0, aludep = 0;
            
            allocate = 0;
            
            for(j=0;j<column_number;j++){
                if(allocate || endArray){
                    break;
                }
                
                for(i=0;i<mem_line;i++){
                    if(arrMap.arrayMatrix[i][j] == 99 && endArray == 0){
                        DPRINTF(AnalysisFlag, "ESPACO ENCONTRADO EM:[%d][%d]\n", i,j);
                        allocate = 1;
                        
                        for(x=0;x<line_number;x++){
                            if(((arrMap.arrayMatrix[x][j] == InstRegs.rs1) && InstRegs.rs1 != 99) ||
                               ((arrMap.arrayMatrix[x][j] == InstRegs.rs2) && InstRegs.rs2 != 99) ||
                               ((arrMap.arrayMatrix[x][j] == InstRegs.rs3) && InstRegs.rs3 != 99) ||
                               ((arrMap.arrayMatrix[x][j] == InstRegs.rs4) && InstRegs.rs4 != 99)){
                                
                                allocate = 0;
                                DPRINTF(AnalysisFlag, "DEPENDENCIA ENCONTRADA EM:[%d][%d]\n", x,j);
                                break;
                            }
                        }
                        
                        if(allocate){
                            DPRINTF(AnalysisFlag, "INSTRUCAO ALOCADA EM:[%d][%d] (rd1: %d)\n", i,j, InstRegs.rd1);
                            arrMap.arrayMatrix[i][j] = InstRegs.rd1;
                            break;
                        }
                        else{
                            if(x<mem_line)
                                DPRINTF(AnalysisFlag, "DEPENDENCIA DE ALU\n");
                            else if(x<mult_line)
                                DPRINTF(AnalysisFlag, "DEPENDENCIA DE MEMORIA\n");
                            else if(x<float_line)
                                DPRINTF(AnalysisFlag, "DEPENDENCIA DE MULT\n");
                            else
                                DPRINTF(AnalysisFlag, "DEPENDENCIA DE FLOAT\n");
                            
                            if(j == (column_number - 1)){
                                DPRINTF(AnalysisFlag, "ARRAY COMPLETO\n");
                                arrayFull = 1;
                                endArray = 1;
                                break;
                            }
                        }
                    }
                    
                    if(allocate || endArray){
                        break;
                    }
                }
            }
        }
        else if(instType == "MemRead" || instType == "MemWrite" || instType == "FloatMemRead" || instType == "FloatMemWrite"){
            DPRINTF(AnalysisFlag, "Acesso a memoria\n");

            for(j=0;j<(column_number - 3);j=j+3){
                if(endArray){
                   break;
                }

                int m = 0;

                for(m=mem_line;m<mult_line;m++){
                    if(arrMap.arrayMatrix[m][j] == 99 && endArray == 0){
                        for(i=0;i<m;i++){
                            if((arrMap.arrayMatrix[i][j] == InstRegs.rs1 || arrMap.arrayMatrix[i][j+1] == InstRegs.rs1 || arrMap.arrayMatrix[i][j+2] == InstRegs.rs1) && InstRegs.rs1 != 99){
                                allocate = 0;
                                break;
                            }
                            else if((arrMap.arrayMatrix[i][j] == InstRegs.rs2 || arrMap.arrayMatrix[i][j+1] == InstRegs.rs2 || arrMap.arrayMatrix[i][j+2] == InstRegs.rs2) && InstRegs.rs2 != 99){
                                allocate = 0;
                                break;
                            }
                            else if((arrMap.arrayMatrix[i][j] == InstRegs.rs3 || arrMap.arrayMatrix[i][j+1] == InstRegs.rs3 || arrMap.arrayMatrix[i][j+2] == InstRegs.rs3) && InstRegs.rs3 != 99){
                                allocate = 0;
                                break;
                            }
                            else if((arrMap.arrayMatrix[i][j] == InstRegs.rs4 || arrMap.arrayMatrix[i][j+1] == InstRegs.rs4 || arrMap.arrayMatrix[i][j+2] == InstRegs.rs4) && InstRegs.rs4 != 99){
                                allocate = 0;
                                break;
                            }
                            else{
                                allocate = 1;
                                break;
                            }
                        }
                        if(allocate == 1){
                            break;
                        }
                    }
                }

                if(allocate == 0 && j > (column_number - 4)){
                    arrayFull = 1;
                    endArray = 1;
                    
                    DPRINTF(AnalysisFlag, "if(allocate == 0 && j > (column_number - 4))\n");
                    
                    break;
                }
 
                if(allocate == 1){
                    arrMap.arrayMatrix[m][j] = InstRegs.rd1;
                    arrMap.arrayMatrix[m][j+1] = InstRegs.rd1;
                    arrMap.arrayMatrix[m][j+2] = InstRegs.rd1;
                    
                    // DEBUG
                    if(instType == "MemWrite"){
                        arrMap.arrayMatrix[m][j] = 88;
                        arrMap.arrayMatrix[m][j+1] = 88;
                        arrMap.arrayMatrix[m][j+2] = 88;
                        
                        DPRINTF(AnalysisFlag, "%d %d  %d %d %d %d\n", InstRegs.rd1, InstRegs.rd2, InstRegs.rs1, InstRegs.rs2, InstRegs.rs3, InstRegs.rs4);
                    }
                    
                    DPRINTF(AnalysisFlag, "INSTRUCAO ALOCADA EM:[%d][%d-%d] (rd1: %d)\n", m,j, j+2,   InstRegs.rd1);
                    break;
                }
            }
        }
        else if(instType == "IntMult" || instType == "IntDiv"){
            DPRINTF(AnalysisFlag, "Acesso a multiplicador/divisor\n");

            for(j=0;j<(column_number - 3);j=j+3){
                if(endArray){
                   break;
                }

                int m = 0;

                for(m=mult_line;m<float_line;m++){
                    if(arrMap.arrayMatrix[m][j] == 99 && endArray == 0){
                        for(i=0;i<m;i++){
                            if((arrMap.arrayMatrix[i][j] == InstRegs.rs1 || arrMap.arrayMatrix[i][j+1] == InstRegs.rs1 || arrMap.arrayMatrix[i][j+2] == InstRegs.rs1) && InstRegs.rs1 != 99){
                                allocate = 0;
                                break;
                            }
                            else if((arrMap.arrayMatrix[i][j] == InstRegs.rs2 || arrMap.arrayMatrix[i][j+1] == InstRegs.rs2 || arrMap.arrayMatrix[i][j+2] == InstRegs.rs2) && InstRegs.rs2 != 99){
                                allocate = 0;
                                break;
                            }
                            else if((arrMap.arrayMatrix[i][j] == InstRegs.rs3 || arrMap.arrayMatrix[i][j+1] == InstRegs.rs3 || arrMap.arrayMatrix[i][j+2] == InstRegs.rs3) && InstRegs.rs3 != 99){
                                allocate = 0;
                                break;
                            }
                            else if((arrMap.arrayMatrix[i][j] == InstRegs.rs4 || arrMap.arrayMatrix[i][j+1] == InstRegs.rs4 || arrMap.arrayMatrix[i][j+2] == InstRegs.rs4) && InstRegs.rs4 != 99){
                                allocate = 0;
                                break;
                            }
                            else{
                                allocate = 1;
                                break;
                            }
                       }
                       if(allocate == 1){
                            break;
                       }


                    }
                }

                if(allocate == 0 && j > (column_number - 4)){
                    arrayFull = 1;
                    endArray = 1;
                    
                    DPRINTF(AnalysisFlag, "if(allocate == 0 && j > (column_number - 4))\n");
                    
                    break;
                }
 
                if(allocate == 1){
                    arrMap.arrayMatrix[m][j] = InstRegs.rd1;
                    arrMap.arrayMatrix[m][j+1] = InstRegs.rd1;
                    arrMap.arrayMatrix[m][j+2] = InstRegs.rd1;
                    
                    DPRINTF(AnalysisFlag, "INSTRUCAO ALOCADA EM:[%d][%d-%d] (rd1: %d)\n", m,j, j+2,   InstRegs.rd1);
                    break;
                }
            }
        }
        else{
            DPRINTF(AnalysisFlag, "Acesso a float\n");
            
            for(j=0;j<(column_number - 6);j=j+3){
                if(endArray){
                   break;
                }
                
                int m = 0;
                
                for(m=float_line;m<line_number;m++){
                    if(arrMap.arrayMatrix[m][j] == 99 && endArray == 0){
                        for(i=0;i<m;i++){
                            if((arrMap.arrayMatrix[i][j] == InstRegs.rs1 || arrMap.arrayMatrix[i][j+1] == InstRegs.rs1 || arrMap.arrayMatrix[i][j+2] == InstRegs.rs1) && InstRegs.rs1 != 99){
                                allocate = 0;
                                break;
                            }
                            else if((arrMap.arrayMatrix[i][j] == InstRegs.rs2 || arrMap.arrayMatrix[i][j+1] == InstRegs.rs2 || arrMap.arrayMatrix[i][j+2] == InstRegs.rs2) && InstRegs.rs2 != 99){
                                allocate = 0;
                                break;
                            }
                            else if((arrMap.arrayMatrix[i][j] == InstRegs.rs3 || arrMap.arrayMatrix[i][j+1] == InstRegs.rs3 || arrMap.arrayMatrix[i][j+2] == InstRegs.rs3) && InstRegs.rs3 != 99){
                                allocate = 0;
                                break;
                            }
                            else if((arrMap.arrayMatrix[i][j] == InstRegs.rs4 || arrMap.arrayMatrix[i][j+1] == InstRegs.rs4 || arrMap.arrayMatrix[i][j+2] == InstRegs.rs4) && InstRegs.rs4 != 99){
                                allocate = 0;
                                break;
                            }
                            else{
                                allocate = 1;
                                break;
                            }
                        }
                        if(allocate == 1){
                            break;
                        }
                    }
                }
                
                if(allocate == 0 && j > (column_number - 4)){
                    arrayFull = 1;
                    endArray = 1;
                    
                    DPRINTF(AnalysisFlag, "if(allocate == 0 && j > (column_number - 4))\n");
                    
                    break;
                }
                
                if(allocate == 1){
                    arrMap.arrayMatrix[m][j] = InstRegs.rd1;
                    arrMap.arrayMatrix[m][j+1] = InstRegs.rd1;
                    arrMap.arrayMatrix[m][j+2] = InstRegs.rd1;
                    arrMap.arrayMatrix[m][j+3] = InstRegs.rd1;
                    arrMap.arrayMatrix[m][j+4] = InstRegs.rd1;
                    arrMap.arrayMatrix[m][j+5] = InstRegs.rd1;
                    
                    DPRINTF(AnalysisFlag, "INSTRUCAO ALOCADA EM:[%d][%d-%d] (rd1: %d)\n", m,j, j+5,   InstRegs.rd1);
                    break;
                }
            }
        }
        
        if(endArray)
            DPRINTF(AnalysisFlag, "Array Completo\n");
    }
    
    if(endArray == 1 && finTick == inTick){
        endArray = 0;
        initArray = 0;
        configStart = 0;
        
        for(i=0;i<line_number;i++){
            for(j=0;j<column_number;j++){
                 arrMap.arrayMatrix[i][j] = 99;
            }
        }
        
        arrMap.afterbranchId = 0;
    }
    if(endArray == 1){
        endArray = 0;
        initArray = 0;
        
        finTick = currentTick;
        
        totalConfigs = totalConfigs + 1;
        //outs << "Config Number: " << totalConfigs << "\n";
        DPRINTF(AnalysisFlag, "Config Number: %ld\n", totalConfigs);
        
        //outs << "FIM DE UMA CONFIGURACAO:    " << currentTick << "\n";
        DPRINTF(AnalysisFlag, "FIM DE UMA CONFIGURACAO:    %d\n", currentTick);
            
        //outs << "Ticks Totais no Processador:    " << (finTick - inTick) << "\n";
        DPRINTF(AnalysisFlag, "Ticks Totais no Processador:    %d\n", (finTick - inTick));


        DPRINTF(AnalysisFlag, "END ARRAY: Ticks Totais no Processador: %d\n", (finTick - inTick));
        int colunaTemp = 0;
        colunasArr = 0;
        
        BTCGRACache.write();
        
        
        for(i=0;i<line_number;i++){
            for(j=0;j<column_number;j++){
                if(arrMap.arrayMatrix[i][j] != 99){
                    colunaTemp= j+1;
                }
            }
            if(colunasArr < colunaTemp){
                colunasArr = colunaTemp;
            }
        }
        
        if(init_conf == 1){
            indice_menor = 0;
            
            for(i=0;i<n;i++){
                if(memoriaConfig[i].afterbranchId == 0){
                    indice_menor = i;
                    init_conf = 0;
                    
                    //outs << "Indice Menor Escolhido:    " << indice_menor << "\n";
                    DPRINTF(AnalysisFlag, "Indice Menor Escolhido:    %d\n", indice_menor);
                    
                    DPRINTF(AnalysisFlag, "Decisao por memoria livre\n");
                    
                    break;
                }
                
                //LRU
                if(memoriaConfig[i].inTick < memoriaConfig[indice_menor].inTick)
                    indice_menor = i;
            }
            
            if(executaILP)
                DPRINTF(AnalysisFlag, "subs conf %d: %ld\n", indice_menor, memoriaConfig[indice_menor].afterbranchId);
            
            //Zera variaveis de configuracao
            memoriaConfig[indice_menor].afterbranchId = 0;
            memoriaConfig[indice_menor].lastID = 0;
            memoriaConfig[indice_menor].accesses = 0;
            memoriaConfig[indice_menor].inTick = 0;
            memoriaConfig[indice_menor].finTick = 0;
            memoriaConfig[indice_menor].configCycles = 0;
            memoriaConfig[indice_menor].specDeep = 0;
            
            memoriaConfig[indice_menor].lastInstId = 0;
            memoriaConfig[indice_menor].continues = 0;

            for(j=0;j<num_regs_proc;j++){
                memoriaConfig[indice_menor].readReg[j] = 0;
                memoriaConfig[indice_menor].writeReg[j] = 0;
            }

            for(j=0;j<line_number;j++){
                for(k=0;k<column_number;k++){
                    memoriaConfig[indice_menor].arrayMatrix[j][k] = 0; 
               }
            }
        }
        else{
            DPRINTF(AnalysisFlag, "else  init_conf == 0\n");
        }
        
        memoriaConfig[indice_menor].lastInstId = instAddress;
        
        
        
        
        int lastPart = 0;
        
        if(arrayFull == 0 && (memoriaConfig[indice_menor].afterbranchId == arrMap.afterbranchId)){
            lastPart = 1;
            
            //outs << "ENTROU NA PRIMEIRA ITERACAO" << "\n";
            DPRINTF(AnalysisFlag, "ENTROU NA PRIMEIRA ITERACAO\n");
        }
        
        if(arrayFull == 0 && lastPart == 0){
            //outs << "ENTROU NA SEGUNDA ITERACAO" << "\n";
            DPRINTF(AnalysisFlag, "ENTROU NA SEGUNDA ITERACAO\n");
            
            
            //outs << "Indice Menor ArrayFull = 0   " << indice_menor << "\n";
            //outs << "Last Part =   " << lastPart << "\n";
            DPRINTF(AnalysisFlag, "Indice Menor ArrayFull = 0   %d\n", indice_menor);
            DPRINTF(AnalysisFlag, "Last Part =   %d\n", lastPart);
            
            
            memoriaConfig[indice_menor].afterbranchId = arrMap.afterbranchId;
            memoriaConfig[indice_menor].accesses = 1;
            memoriaConfig[indice_menor].inTick = inTick;
            memoriaConfig[indice_menor].finTick = finTick;
            memoriaConfig[indice_menor].lastID = memoriaConfig[indice_menor - 1].afterbranchId;
            memoriaConfig[indice_menor].lastAllocatedColumn = colunasArr;
            
            for(i=0;i<line_number;i++){
               for(j=0;j<column_number;j++){
                   memoriaConfig[indice_menor].arrayMatrix[i][j] = arrMap.arrayMatrix[i][j];
               }
            }
            
            for(i=0;i<num_regs_proc;i++){
                memoriaConfig[indice_menor].readReg[i] = regRead[i];
                regRead[i] = 0;
                memoriaConfig[indice_menor].writeReg[i] = regWrite[i];
                regWrite[i] = 0;   
            }
            
            contadorWb = 0;
            contadorSr = 0;
            wbCycles = 0;
            srCycles = 0;
            
            arrayCycle = 0;
            
            for(i=0;i<num_regs_proc;i++){
                if(memoriaConfig[indice_menor].writeReg[i] == 1){
                    contadorWb = contadorWb + 1;         
                }
                if(memoriaConfig[indice_menor].readReg[i] == 1){
                    contadorSr = contadorSr + 1;         
                }
                //outs << "ReadReg[" << i << "]: " << aux->readReg[i] << "\n";
                //outs << "WriteReg[" << i << "]: " << aux->writeReg[i] << "\n";
            }
            
            
            configStart = 0;
            
            if(specDeep == 3){
                specDeep = 0;
                memoriaConfig[indice_menor].specDeep = 2;
            }
            else{
                specDeep++;
                memoriaConfig[indice_menor].specDeep = 1;
            }
            
            
            if(contadorWb%reg_per_cycle == 0){
                 wbCycles = contadorWb/reg_per_cycle;
            }
            else{
                 wbCycles = (contadorWb/reg_per_cycle) + 1;
            }
            
            if(contadorSr%reg_per_cycle == 0){
                srCycles = contadorSr/reg_per_cycle;
            }
            else{
                srCycles = (contadorSr/reg_per_cycle) + 1;
            }
            
            
            if(colunasArr%3 == 0){
                arrayCycle = colunasArr/3;
            }
            else{
                arrayCycle = (colunasArr/3) + 1;
            }
            
            
            if(wbCycles == 0 && srCycles == 0){
                arrayCycle = 0;
            }
            
            memoriaConfig[indice_menor].configCycles = wbCycles + srCycles + arrayCycle;
            
            DPRINTF(AnalysisFlag, "ConfigArrayFull =   %ld\n", memoriaConfig[indice_menor].configCycles);
            DPRINTF(AnalysisFlag, "contadorSr: %d\n", contadorSr);
            DPRINTF(AnalysisFlag, "contadorWb: %d\n", contadorWb);
            DPRINTF(AnalysisFlag, "contadorAr: %d\n", colunasArr);
        }

        if(arrayFull == 1 || lastPart == 1){
            /*
            outs << "ENTROU NA TERCEIRA ITERACAO" << "\n";
            outs << "ARRAY FULL  =  " << arrayFull << "\n";
            outs << "LAST PART  =  " << lastPart << "\n";

            outs << "Indice Menor ArrayFull = 1   " << indice_menor << "\n";
            outs << "Last Part =   " << lastPart << "\n";
            */
            
            DPRINTF(AnalysisFlag, "ENTROU NA TERCEIRA ITERACAO\n");
            DPRINTF(AnalysisFlag, "ARRAY FULL =   %d\n", arrayFull);
            DPRINTF(AnalysisFlag, "LAST PART =   %d\n", lastPart);
            
            DPRINTF(AnalysisFlag, "Indice Menor ArrayFull = 1   %d\n", indice_menor);
            DPRINTF(AnalysisFlag, "Last Part =   %d\n", lastPart);
            
            
            
            memoriaConfig[indice_menor].afterbranchId = arrMap.afterbranchId;
            memoriaConfig[indice_menor].accesses = 1;
            
            memoriaConfig[indice_menor].continues = 1;

            //memoriaConfig[indice_menor].lastID = memoriaConfig[indice_menor - 1].afterbranchId;

            for(i=0;i<line_number;i++){
               for(j=0;j<column_number;j++){
                   memoriaConfig[indice_menor].arrayMatrix[i][j] = arrMap.arrayMatrix[i][j];
               }
            }

     
            for(i=0;i<num_regs_proc;i++){
                if(memoriaConfig[indice_menor].readReg[i] == regRead[i] && regRead[i] == 1){
                    contregRead[i] = 0;
                }
                else{
                    contregRead[i] = regRead[i];
                }

                if(memoriaConfig[indice_menor].readReg[i] == 1){
                    memoriaConfig[indice_menor].readReg[i] = 1;                   
                }
                else{
                    memoriaConfig[indice_menor].readReg[i] = regRead[i];
                }

                regRead[i] = 0;

                if(memoriaConfig[indice_menor].writeReg[i] == regWrite[i] && regWrite[i] == 1){
                    contregWrite[i] = 0;
                }
                else{
                    contregWrite[i] = regWrite[i];
                }

                if(memoriaConfig[indice_menor].writeReg[i] == 1){
                    memoriaConfig[indice_menor].writeReg[i] = 1;                   
                }
                else{
                    memoriaConfig[indice_menor].writeReg[i] = regWrite[i];
                }
                regWrite[i] = 0;   
            }


            if (specDeep == 3){
                memoriaConfig[indice_menor].specDeep = 2;
            }
            else{
                memoriaConfig[indice_menor].specDeep = 1;
            }

            /*
            //outs << "WriteReg =   ";
            DPRINTF(AnalysisFlag, "WriteReg =   \n");
            for(i = 0;i<num_regs_proc;i++){
                //outs << "   " << memoriaConfig[indice_menor].writeReg[i];
                DPRINTF(AnalysisFlag, "   %d\n", memoriaConfig[indice_menor].writeReg[i]);
            }

            //outs << "\n";
            DPRINTF(AnalysisFlag, "\n");

            //outs << "ReadReg =   ";
            DPRINTF(AnalysisFlag, "ReadReg =   \n");

            for(i = 0;i<num_regs_proc;i++){
                //outs << "   " << memoriaConfig[indice_menor].readReg[i];
                DPRINTF(AnalysisFlag, "   %d\n", memoriaConfig[indice_menor].readReg[i]);
            }
            //outs << "\n";
            DPRINTF(AnalysisFlag, "\n");

            //outs << "CountRegRead =   ";
            DPRINTF(AnalysisFlag, "CountRegRead =   \n");
            for(i = 0;i<num_regs_proc;i++){
                //outs << "   " << contregRead[i];
                DPRINTF(AnalysisFlag, "   %d\n", contregRead[i]);
            }
            //outs << "\n";
            DPRINTF(AnalysisFlag, "\n");

            //outs << "CountRegWrite =   ";
            DPRINTF(AnalysisFlag, "CountRegWrite =   \n");
            for(i = 0;i<num_regs_proc;i++){
                //outs << "   " << contregWrite[i];
                DPRINTF(AnalysisFlag, "   %d\n", contregWrite[i]);
            }
            //outs << "\n";
            DPRINTF(AnalysisFlag, "\n");
            */


            configStart = 1;

            if(lastPart == 1){
                memoriaConfig[indice_menor].inTick = inTick;
                
                memoriaConfig[indice_menor].finTick = finTick;
                configStart = 0;
                initArray = 0;
                
                DPRINTF(AnalysisFlag, "if(lastPart == 1)    configStart = 0\n");
            }
            else{
                memoriaConfig[indice_menor].inTick = inTick;
                memoriaConfig[indice_menor].finTick = finTick;
                
                initArray = 1;
                
                init_conf = 1;
                
                DPRINTF(AnalysisFlag, "else(lastPart == 1)    configStart = 0\n");
            }

            contadorWb = 0;
            contadorSr = 0;
            wbCycles = 0;
            srCycles = 0;

            arrayCycle = 0;

            for(i=0;i<num_regs_proc;i++){
                if(contregWrite[i] == 1){
                    contadorWb = contadorWb + 1;         
                }
                if(contregRead[i] == 1){
                    contadorSr = contadorSr + 1;         
                }
                //outs << "ReadReg[" << i << "]: " << aux->readReg[i] << "\n";
                //outs << "WriteReg[" << i << "]: " << aux->writeReg[i] << "\n";
            }

            if(contadorWb%reg_per_cycle == 0){
                 wbCycles = contadorWb/reg_per_cycle;
            }
            else{
                 wbCycles = (contadorWb/reg_per_cycle) + 1;
            }

            if(contadorSr%reg_per_cycle == 0){
                srCycles = contadorSr/reg_per_cycle;
            }
            else{
                srCycles = (contadorSr/reg_per_cycle) + 1;
            }

     
            if(colunasArr%3 == 0){
                arrayCycle = colunasArr/3;
            }
            else{
                arrayCycle = (colunasArr/3) + 1;
            }

            if(wbCycles == 0 && srCycles == 0){
                arrayCycle = 0;
            }

            memoriaConfig[indice_menor].configCycles = memoriaConfig[indice_menor].configCycles + wbCycles + srCycles + arrayCycle;

            /*
            outs << "ConfigArrayFull =   " << memoriaConfig[indice_menor].configCycles << "\n";                  
            outs << "contadorSr: " << contadorSr << "\n";
            outs << "contadorWb: " << contadorWb << "\n";
            outs << "contadorAr: " << colunasArr << "\n";
            */
            DPRINTF(AnalysisFlag, "ConfigArrayFull =   %ld\n", memoriaConfig[indice_menor].configCycles);
            DPRINTF(AnalysisFlag, "contadorSr: %d\n", contadorSr);
            DPRINTF(AnalysisFlag, "contadorWb: %d\n", contadorWb);
            DPRINTF(AnalysisFlag, "contadorAr: %d\n", colunasArr);
        }

        //outs << indice_menor << "\n";
        DPRINTF(AnalysisFlag, "indice_menor: %d\n", indice_menor);
        
        
        //printaArray(indice_menor);
        
        /*
        ostream &outs = Trace::output();
        
        int aux=0, aux2=0;
       
        while(aux < n)
        {
            if(memoriaConfig[aux].afterbranchId != 0){
                for(i=0;i<line_number;i++){
                    aux2 = 0;
                    for(j=0;j<column_number;j++){
                        if(j == 0 && i == 0){
                            outs << " ALU:" << "\t|\t";
                        }
                        if(j == 0 && i == 1){
                            outs << " ALU:" << "\t|\t";
                        }
                        if(j == 0 && i >= 2){
                            outs << " MEM:" << "\t|\t";
                        }
                        if(aux2 == 3){
                            outs << "|";
                            outs << "\t";
                            aux2 = 0;
                        }
                        aux2 = aux2 + 1;
                        //outs << memoriaConfig[aux].arrayMatrix[i][j] << "   ";
                        
                        if(memoriaConfig[index_hit].arrayMatrix[i][j] != 99)
                            ccprintf(outs, "%d\t", memoriaConfig[index_hit].arrayMatrix[i][j]);
                        else
                            outs << "X\t";
                    }
                    outs << "\n";
                }
                outs << "\n";

                
                //outs << "ID:  " << memoriaConfig[aux].afterbranchId;
                //outs << "\n";
                //outs << "Last ID:  " << memoriaConfig[aux].lastID;
                //outs << "\n";
                //outs << "ConfigCycles:  " << memoriaConfig[aux].configCycles;
                //outs << "\n";
                //outs << "SpecDeep:  " << memoriaConfig[aux].specDeep;
                //outs << "\n";
                
                DPRINTF(AnalysisFlag, "ID:  %x\n", memoriaConfig[aux].afterbranchId);
                DPRINTF(AnalysisFlag, "Last ID:  %x\n", memoriaConfig[aux].lastID);
                DPRINTF(AnalysisFlag, "ConfigCycles:  %d\n", memoriaConfig[aux].configCycles);
                DPRINTF(AnalysisFlag, "SpecDeep:  %d\n", memoriaConfig[aux].specDeep);
                

                if(funct == "_Exit"){
                    //outs << "Configuracao:   " << aux << "\n";
                    //outs << "Tick Difference:  " << (memoriaConfig[aux].finTick - memoriaConfig[aux].inTick) << "\n";
                    //outs << "Config Tick:  " <<  memoriaConfig[aux].configCycles*CLOCKPERIOD << "\n";
                    
                    DPRINTF(AnalysisFlag, "Configuracao:  %d\n", aux);
                    DPRINTF(AnalysisFlag, "Tick Difference:  %ld\n", (memoriaConfig[aux].finTick - memoriaConfig[aux].inTick));
                    DPRINTF(AnalysisFlag, "Config Tick:  %ld\n", memoriaConfig[aux].configCycles*CLOCKPERIOD);
                }
                
                //outs << "InTick:  " << memoriaConfig[aux].inTick << "\n";
                //outs << "OutTick:  " << memoriaConfig[aux].finTick << "\n";
                
                DPRINTF(AnalysisFlag, "InTick:  %ld\n", memoriaConfig[aux].inTick);
                DPRINTF(AnalysisFlag, "OutTick:  %ld\n", memoriaConfig[aux].finTick);
            }

            aux = aux + 1;      
        }
        */
        

        for(i=0;i<line_number;i++){
            for(j=0;j<column_number;j++){
                 arrMap.arrayMatrix[i][j] = 99;
            }
        }
        
        arrMap.afterbranchId = 0;
    }

    /*
    DPRINTF(AnalysisFlag, "--------------------------------------------------------------------------------------------------\n");


    DPRINTF(ResultsFlag, "ECONOMIA TOTAL: %lld\n", economiaTotal);
    outs << "\n";

    outs << "\n";
    outs << currentTick << ":    " << "ECONOMIA TOTAL:  " << economiaTotal << "\n";

    DPRINTF(ResultsFlag, "INSTRUCAO ATUAL: %s\n", fullInstruction);
    */
    
    int index_p = 0, economy_cycles_no_spec = 0;

    while(index_p < n)
    {
        if(memoriaConfig[index_p].afterbranchId != 0){
            if(funct == "_Exit"){
                /*
                outs << "Configuracao:   " << index_p << "\n";
                outs << "Tick Difference:  " << (memoriaConfig[index_p].finTick - memoriaConfig[index_p].inTick) << "\n";
                outs << "Config Tick:  " <<  memoriaConfig[index_p].configCycles*CLOCKPERIOD << "\n";
                outs << "Total Accesses:  " <<  memoriaConfig[index_p].accesses << "\n"; 
                outs << "__________________________________________________________\n\n";
                */
                DPRINTF(AnalysisFlag, "Configuracao:   %d\n", index_p);
                DPRINTF(AnalysisFlag, "Tick Difference:   %ld\n", (memoriaConfig[index_p].finTick - memoriaConfig[index_p].inTick));
                DPRINTF(AnalysisFlag, "Config Tick:   %ld\n", memoriaConfig[index_p].configCycles*CLOCKPERIOD);
                DPRINTF(AnalysisFlag, "Total Accesses:   %d\n", memoriaConfig[index_p].accesses);
                DPRINTF(AnalysisFlag, "__________________________________________________________\n\n");
                
                
                economy_cycles_no_spec = economy_cycles_no_spec + (memoriaConfig[index_p].accesses - 1)*((memoriaConfig[index_p].finTick - memoriaConfig[index_p].inTick) - memoriaConfig[index_p].configCycles*CLOCKPERIOD);
                       
            }                                   
        }

        index_p = index_p + 1;
    }

    //ostream &outs = Trace::output();

    /*
    DPRINTF(ResultsFlag, "INSTRUCAO ATUAL: %s\n", instruction);
    DPRINTF(ResultsFlag, "TIPO DE INSTRUCAO: %s\n", Enums::OpClassStrings[inst->opClass()]);
    DPRINTF(ResultsFlag, "TICKS TOTAIS CONFIGURACOES: %d\n", totalTick);
    DPRINTF(ResultsFlag, "NUMERO DE CONFIGURACOES: %d\n", totalConfigs);
    DPRINTF(ResultsFlag, "NUMERO DE HITS: %d\n", totalHits);
    DPRINTF(ResultsFlag, "TOTAL DE BLOCOS CONTINUADOS: %d\n", totalcontBlocks);
    DPRINTF(ResultsFlag, "NUMERO DE INSTRUCOES: %d\n", totalInst);
    DPRINTF(ResultsFlag, "NUMERO DE INSTRUCOES CONDICIONAIS: %d\n", condinstCount);
    DPRINTF(ResultsFlag, "NUMERO DE ALU: %d\n", totalALU);
    DPRINTF(ResultsFlag, "NUMERO DE MEM: %d\n", totalMEM);
    DPRINTF(ResultsFlag, "NUMERO DE BRANCHES: %d\n", totalCond);
    DPRINTF(ResultsFlag, "NUMERO DE OTHERS: %d\n", totalOther);
    */
    //outs << currentTick << ":    " << "ECONOMIA TOTAL:  " << economiaTotal << "\n\n";
    
    DPRINTF(AnalysisFlag, "fim ilp\n");
}



void Trace::ExeTracerRecord::dump()
{
    if (Debug::ExecMacro && staticInst->isMicroop() &&
        ((Debug::ExecMicro &&
            macroStaticInst && staticInst->isFirstMicroop()) ||
            (!Debug::ExecMicro &&
             macroStaticInst && staticInst->isLastMicroop()))) {
        traceInst(macroStaticInst, false);
    }
    if (Debug::ExecMicro || !staticInst->isMicroop()) {
        traceInst(staticInst, true);
    }
}

} // namespace Trace

Trace::ExeTracer *ExeTracerParams::create()
{
    return new Trace::ExeTracer(this);
}
