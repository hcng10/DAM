from __future__ import absolute_import
from __future__ import print_function
import sys
import os
from optparse import OptionParser
from os import listdir
from os.path import isfile, join
import copy

# the next line can be removed after installation
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import pyverilog.utils.version
import pyverilog.utils.signaltype as signaltype
from pyverilog.dataflow.dataflow_analyzer import VerilogDataflowAnalyzer
from pyverilog.dataflow.optimizer import VerilogDataflowOptimizer
from pyverilog.dataflow.dataflow_codegen import VerilogCodeGenerator
from pyverilog.dataflow.dataflow import  MuxIdfy
from pyverilog.dataflow.vmerge_var import  *
from pyverilog.dataflow.dataflow import  DesignBindDest

from generateMuxTemplate import *


ConcatFile = "~/ICL/overlay/muxExample/concat.v"
ConcatFileTop = "concat"

PartSelectFile = "~/ICL/overlay/muxExample/partselect.v"
PartSelectFileTop = "partselect"

MuxFile = "mux.v"


def generateDataFlow(filelist, topmodule, noreorder, nobind, preprocess_include, preprocess_define):

    analyzer = VerilogDataflowAnalyzer(filelist, topmodule, noreorder, nobind, preprocess_include, preprocess_define)
    analyzer.generate()

    return analyzer


"""
    Get the list of signals from each design, and compared it with the signal previous designs
    If there is a different for a particular signal, store the difference in sigdiffScope_Ref0,
    Bascially sigdiffScope_Ref0 stores the diff when compared with the first bitwidth

    analyzer: the parsed object
    designterm_list: list of signals in one design
    idx: the design no. that you are now processing
    sigdiffScope_Ref0: the dict that will contain the signal where the bitwidth is different across different design
            sigdiffScope_Ref0['signal_name'][0,1,2.....], where the sigdiffScope_Ref0['signal_name'][0] set the reference val

    Complexity: O(No. of signals * no. of designs)
"""
def createSignalList(analyzer, designterm_list, idx, sigdiffScope_Ref0, sigStr_Type):

    instances = analyzer.getInstances()
    
    print('Instance: ')
    for module, instname in sorted(instances, key=lambda x: str(x[1])):
        print((module, instname))

    term = analyzer.getTerms()
    #designterm_list[idx] = term
    designterm_list.append(term)

    #calculate the bitnum
    for tk, tv in term.items():
        tv.bitwidth = tv.msb.eval() - tv.lsb.eval() + 1
        #print(tv.bitwidth, tk)

    if idx > 0:
        #check the diff in port no. between signals, the bitwidth in design0 is set as ref :D
        for tk, tv in term.items():

            preterm = designterm_list[idx-1][tk]

            #if the bitwidth is the same, you still need to check if any of the previous signal is diff
            if preterm.bitwidth == tv.bitwidth:
                if tk in sigdiffScope_Ref0:
                    sigdiffScope_Ref0[tk][idx] = sigdiffScope_Ref0[tk][idx-1]
            else:
                if tk in sigdiffScope_Ref0:
                    sigdiffScope_Ref0[tk][idx] = tv.bitwidth - (preterm.bitwidth - sigdiffScope_Ref0[tk][idx - 1] )
                else:
                    for i in xrange(0, idx):
                        if i == 0:
                            sigdiffScope_Ref0[tk] = []
                            #sigdiffScope_Ref0[tk][i] = preterm.bitwidth
                            sigdiffScope_Ref0[tk].append(preterm.bitwidth)
                        else:
                            #sigdiffScope_Ref0[tk][i] = 0
                            sigdiffScope_Ref0[tk].append(0)


                    sigdiffScope_Ref0[tk].append(tv.bitwidth - preterm.bitwidth)

                    sigStr_Type[str(tk)] = copy.deepcopy(tv.termtype)
                    if signaltype.isReg(sigStr_Type[str(tk)]): sigStr_Type[str(tk)].remove('Reg')

    print('Term:')
    for tk, tv in term.items():
        print(tk, tv.tostr())

    print(' ')


"""
    Base on sigdiffScope_Ref0, we want to find out the different between the max-bitwidth and the other bitwidth across
    various designs

    sigdiffScope_Ref0: the dict that will contain the signal where the bitwidth is different across different design
            sigdiffScope_Ref0['signal_name'][0,1,2.....], where the sigdiffScope_Ref0['signal_name'][0] set the reference val

    sigdiffStr_Refmax: the dict that tells us the diff between mine and the max bitwidth, 0 means no diff.

    Complexity: O(No. of signals * no. of designs)
"""

def findsigdiffStr_Refmax(sigdiffScope_Ref0, sigdiffStr_Refmax, sigdiffStr_Maxbit, sigdiffStr_Maxbit_Design):

    for tk, tv in sigdiffScope_Ref0.items():

        ref0bit = tv[0]

        maxbit = tv[0]
        maxpos = 0
        for i, e in enumerate(tv):
            if i > 0 and ref0bit + e > maxbit:
                maxbit = ref0bit + e
                maxpos = i

        tk_str = str(tk)
        sigdiffStr_Refmax[tk_str] = []
        bitdiffval = 0
        for i, e in enumerate(tv):
            if i == 0:
                bitdiffval = 0 if maxpos == i else e - maxbit
                #sigdiffStr_Refmax[tk_str][i] = 0 if maxpos == i else e - maxbit
            else:
                bitdiffval = 0 if maxpos == i else (ref0bit + e) - maxbit
                #sigdiffStr_Refmax[tk_str][i] = 0 if maxpos == i else (ref0bit + e) - maxbit
            sigdiffStr_Refmax[tk_str].append(bitdiffval)

            if bitdiffval == 0: sigdiffStr_Maxbit_Design[tk_str] = i

        sigdiffStr_Maxbit[tk_str] = maxbit




def chgBindDestAfterMuxGen(options, design, bindlist, bindMuxinfodict_list, sigdiffStr_Refmax, sigdiffStr_Maxbit, concatanalyzer, partselectanalyzer):
    for i in range(len(bindlist) - 1, -1, -1):
        bi = bindlist[i][0]
        bv = bindlist[i][1]

        bi_str = str(bi)
        bindMuxinfo = bindMuxinfodict_list[design][bi_str]
        bindBrIdfyDict = bindMuxinfo.brIdfyDict

        # (5-a) Consider the head-is-multi case
        if bi_str in sigdiffStr_Refmax:
            # (5-aI)    case 1: tree common, but with multi-bit and compare
            if bindMuxinfo.termMultiNum > 0 and bindMuxinfo.hasCmp:
                #TODO: Improve the compare mechanism in the future
                # if you have 'compare' in bindtree, we separate that to TWO bindtree to make things simple
                muxingscope = bi.scopechain[-1]
                muxingscope.scopename = muxingscope.scopename + "_mux" + str(design)

                for bve in bv:
                    bve.bindDestVModify(BIND_CHILD_WITH_MULTI, options, design, concatanalyzer, partselectanalyzer,
                                        sigdiffStr_Refmax, sigdiffStr_Maxbit)

            # (5-aII) case 2: entire tree common but no multi-bit
            #                 no need to care about 'compare' as well, bcos the subtree is essentially the same
            #         case 3: tree common, with multi-bit but no cmp
            else:
                # Design 0, change the head only, no need to change subtree
                if design == 0:
                    muxingscope = bi.scopechain[-1]
                    muxingscope.scopename = muxingscope.scopename + "_mux"
                else:
                    # other designs, delete that head and subtree
                    del bindlist[i]


        # TODO: for the rest of the signals, we take care of that later
        """
        else:
            designdiffscope = bi.scopechain[-1]
            designdiffscope.scopename = designdiffscope.scopename + str(design)

            for bve in bv:
                bve.bindDestVModify(BIND_DESIGN_DIFF, options, design, None, partselectanalyzer, sigdiffStr_Refmax, sigdiffStr_Maxbit)
        """
        # (5-b) take care the branch portion in the tree, since the conditional is usually evaluated to 1-bit,
        #       we don't need to consider bi, I think
        for bve in bv:
            bve.bindDestBrModify(options, bindBrIdfyDict, design, partselectanalyzer, sigdiffStr_Refmax, sigdiffStr_Maxbit, False)



def chgTermsAfterMuxGen(design, termdict, bindMuxinfodict_list, sigdiffStr_Refmax, sigdiffStr_Maxbit_Design,
                                                                    muxterm_dict, muxtermStr_ind_dict, options):
    # in TERMs, the format is [scope: signals]
    for ti, tv in termdict.items():
        ti_str = str(ti)

        # some signals are not in the bindlist, such as inputs
        if ti_str in bindMuxinfodict_list[design]:
            bindMuxinfo = bindMuxinfodict_list[design][ti_str]

            # (6-a) Consider the head-is-multi case
            if ti_str in sigdiffStr_Refmax:

                # (6-aI) case 1: tree common, but with multi-bit and compare
                if  bindMuxinfo.termMultiNum > 0 and bindMuxinfo.hasCmp:
                    muxingscope = ti.scopechain[-1]
                    muxingscope.scopename = muxingscope.scopename + "_mux" + str(design)

                    deleteMuxTerm(ti, muxtermStr_ind_dict, muxterm_dict)

                # (6-aI) case 2: tree common, but with multi-bit and no compare
                #        case 3: entire tree common but no multi-bit
                else:
                    # Such complicated check is required because the max signals bitwidth can be the same in two designs
                    if sigdiffStr_Refmax[ti_str][design] == 0 and sigdiffStr_Maxbit_Design[ti_str] == design:
                        muxingscope = ti.scopechain[-1]
                        muxingscope.scopename = muxingscope.scopename + "_mux"
                        # (6-aIII) compare with the signal in muxterms_dict, remove when needed
                        deleteMuxTerm(ti, muxtermStr_ind_dict, muxterm_dict)

                    else:
                        # other designs, delete that signal
                        del termdict[ti]

                # If 'mux' is put as postfix, then it will be an input to mux
                # which means it will not be used as IO
                if signaltype.isInput(tv.termtype): tv.termtype.remove('Input')
                elif signaltype.isInout(tv.termtype): tv.termtype.remove('Inout')
                elif signaltype.isOutput(tv.termtype): tv.termtype.remove('Output')


            # (6-b) For other signals, they are added with 0/1/2 as postfix
            """
            else:
                nonmuxingscope = ti.scopechain[-1]
                nonmuxingscope.scopename = nonmuxingscope.scopename + str(design)
            """

        elif ti.scopechain[-1].scopename == options.clockname:
            if not design == 0: del termdict[ti]

        elif ti.scopechain[-1].scopename == options.resetname:
            if not design == 0: del termdict[ti]
        else:
            nonmuxingscope = ti.scopechain[-1]
            nonmuxingscope.scopename = nonmuxingscope.scopename + str(design)




def main():
    INFO = "Verilog designs merger."
    #VERSION = pyverilog.utils.version.VERSION
    USAGE = "Usage: vmerge.py -t TOPMODULE design_dir ..."

    def showVersion():
        print(INFO)
        #print(VERSION)
        print(USAGE)
        sys.exit()
    
    optparser = OptionParser()
    optparser.add_option("-v","--version",action="store_true",dest="showversion",
                         default=False,help="Show the version")
    optparser.add_option("-I","--include",dest="include",action="append",
                         default=[],help="Include path")
    optparser.add_option("-D",dest="define",action="append",
                         default=[],help="Macro Definition")
    optparser.add_option("-t","--top",dest="topmodule",
                         default="TOP",help="Top module, Default=TOP")
    optparser.add_option("--nobind",action="store_true",dest="nobind",
                         default=False,help="No binding traversal, Default=False")
    optparser.add_option("--noreorder",action="store_true",dest="noreorder",
                         default=False,help="No reordering of binding dataflow, Default=False")
    optparser.add_option("--clockname",dest="clockname",
                         default="CLK",help="Clock signal name")
    optparser.add_option("--resetname",dest="resetname",
                         default="RST_X",help="Reset signal name")
    optparser.add_option("--clockedge",dest="clockedge",
                         default="posedge",help="Clock signal edge")
    optparser.add_option("--resetedge",dest="resetedge",
                         default="negedge",help="Reset signal edge")
    optparser.add_option("-s","--search",dest="searchtarget",action="append",
                         default=[],help="Search Target Signal")
    optparser.add_option("-o","--output",dest="outputfile",
                         default="vmerged.v",help="Output File name, Default=vmerged.v")
    (options, args) = optparser.parse_args()

    dirlist = args
    if options.showversion:
        showVersion()

    for d in dirlist:
        if not os.path.exists(d): raise IOError("directory not found: " + d)

    if len(dirlist) == 0:
        showVersion()

    """
    0st: Getting info from dir, ignore the non-verilog file, generate dataflow from each design dir,
        find different in sig bit-width with reference to sig in first design
    """

    filelist = []
    designanalyzer_list = []
    designterm_list = []
    sigdiffScope_Ref0 = {}
    sigStr_Type = {}

    for idx ,dir in enumerate(dirlist):
        #filelist[idx] = [join(dir, x) for x in listdir(dir) if isfile(join(dir, x))]
        filelist.append([join(dir, x) for x in listdir(dir) if isfile(join(dir, x))])

        #remove file without extension v
        eid = 0
        while eid < len(filelist[idx]):
            if not filelist[idx][eid].endswith(".v"):
                filelist[idx].pop(eid)
            else:
                eid = eid + 1


        designanalyzer_list.append(generateDataFlow(filelist[idx], options.topmodule,
                                            noreorder=options.noreorder,
                                            nobind=options.nobind,
                                            preprocess_include=options.include,
                                            preprocess_define=options.define))

        createSignalList(designanalyzer_list[idx], designterm_list, idx, sigdiffScope_Ref0, sigStr_Type)

    """
    1st: Parse a file to obtain concat structure and PartSelect select

    """
    concatanalyzer = generateDataFlow(ConcatFile, ConcatFileTop,
                                            noreorder=False,
                                            nobind=False,
                                            preprocess_include=[],
                                            preprocess_define=[])

    partselectanalyzer = generateDataFlow(PartSelectFile, PartSelectFileTop,
                                            noreorder=False,
                                            nobind=False,
                                            preprocess_include=[],
                                            preprocess_define=[])


    """
    2nd: find different in sig bit-width with reference to max bit-width across design,
        until now we do not need to utilize the bind tree, we just need to navigate TERMS
    """

    sigdiffStr_Refmax = {}
    sigdiffStr_Maxbit = {}
    sigdiffStr_Maxbit_Design = {}
    findsigdiffStr_Refmax(sigdiffScope_Ref0, sigdiffStr_Refmax, sigdiffStr_Maxbit,sigdiffStr_Maxbit_Design)

    #TODO: can be removed***
    print(sigdiffStr_Refmax)
    print(sigdiffStr_Maxbit)



    print('Bind:')
    print(designanalyzer_list[0].getBinddict(), '\n')
    bind_list = sorted(designanalyzer_list[0].getBinddict().items(),key=lambda x:str(x[0]))

    print("bind_list")
    for bi, bv in bind_list:
        for bve in bv:
            print(bi, bve.tostr())

    print('\n')

    # TODO: ***can be removed



    """
    3rd: traverse the bind tree, and get some useful info by :)
        0. get the bind tree first ()
        1. ID multi-node
        2. Count multi-node and constant
    """
    print("\n*************** 3rd Step ***************")

    #3.0: get the bind tree first
    designbindlist_list = []
    for design, analyzer in enumerate(designanalyzer_list):
        # sorting will cause O(nlogn), where n is the number of bindtree (head)
        bindlist = sorted(analyzer.getBinddict().items(),key=lambda x:str(x[0])) #traverse bindtree + 1
        designbindlist_list.append(bindlist)

    #3.1 - 3.2: ID and count multi-node
    #bindMuxinfo = {}
    #info_dict = {}
    bindMuxinfodict_list = []
    infodict_list = []

    for design, bindlist in enumerate(designbindlist_list): #traverse bindtree + 2
        bindMuxinfodict_list.append({})
        infodict_list.append({})

        for bi, bv in bindlist:
            muxIdfy = MuxIdfy(str(bi))
            bindMuxinfodict_list[design][str(bi)] = muxIdfy
            infodict_list[design][str(bi)] = {}

            for bve in bv:
                print("Design", str(design), " bindIdx:", bi, \
                  "\nbindTree:", bve.traverse(sigdiffStr_Refmax, muxIdfy, options, infodict_list[design][str(bi)]))

    # TODO: can be removed***
    # for design, bindMuxinfodict in enumerate(bindMuxinfodict_list):
    #      for bmi, bmv in bindMuxinfodict.items():
    #          print("Design", str(design), " bindMuxIdx:", bmi, "\nbindMux:", bmv.toStr())
            # TODO: ***can be removed


    """
    4nd: create mux data structure with a verilog template by :)
        1. write a template verilog file which contains all the muxes needed
        2. parse that file and get the bind tree data structure
        3. change the data structure accordingly
    """
    print("\n*************** 4th Step ***************")
    print(sigdiffStr_Refmax)
    print(sigdiffStr_Maxbit)
    generateMuxDataStruct(options.topmodule, len(dirlist), designbindlist_list, bindMuxinfodict_list, sigdiffStr_Refmax,
                          sigdiffStr_Maxbit)

    bindMuxinfo = bindMuxinfodict_list[0]#TODO: just getting design 0 is a hack
    [muxterm_dict, muxtermStr_ind_dict, muxtermStr_val_dict, muxbind_dict, muxbindStr_head_dict, muxbindStr_tree_dict] = \
        generateMuxTemplate(options.topmodule, len(dirlist), bind_list, bindMuxinfo, sigdiffStr_Refmax, sigdiffStr_Maxbit, sigStr_Type)



    print("\n*************** 5th Step ***************")
    """
    5. Change the binddest structure (bi, bv) according to step 3.2, which includes:
        ->. handle the case where the head is with multi-bit
        ->. head not multi-bit, so there are two possible scenarios
            (a) head is in part of the common tree
            (b) head is not part of the common tree
        Goal: change the binddest structure so as to place mux and merge design
    """

    # traverse backward so that I can remove the element
    for design, bindlist in enumerate(designbindlist_list):  # traverse bindtree + 4
                                                # (2 times bcos one is the bindtree the other is the branch in bindtree)
        chgBindDestAfterMuxGen(options, design, bindlist, bindMuxinfodict_list, sigdiffStr_Refmax, sigdiffStr_Maxbit, concatanalyzer, partselectanalyzer)



    for design, bindlist in enumerate(designbindlist_list):  # traverse bindtree + 3
        for bi, bv in bindlist:
            print(design, bi)
            for bve in bv:
                print(bve.tostr())

    term = analyzer.getTerms()
    print(">>>>>>>>>>>>>>>>>>>>>>>>>>>>>>", term)



    """
    6th : Now the mux structure is settled, so settle the signals in the main designs to accommodate the muxed signals by :)
        1. merge the term list together for the final output by:
            a. For multi-bit signals, add one more signals and name it as <orignal_signal>_mux
            b. For others, change it to <orignal_signal>_<design_num>
    """
    print("\n*************** 6th Step ***************")
    for design, termdict in enumerate(designterm_list):
        chgTermsAfterMuxGen(design, termdict, bindMuxinfodict_list, sigdiffStr_Refmax, sigdiffStr_Maxbit_Design, \
                                                                muxterm_dict, muxtermStr_ind_dict, options)




    """
    7th : Combine all the term and bindtree into one data structure for code generation

    """
    newtermdict={}
    newbinddict={}
    for design, termdict in enumerate(designterm_list):
        for ti, tv in termdict.items():
            if ti in newtermdict: print("Step7: Warning: repeated terms: ", ti)
            newtermdict[ti] = tv

    for ti, tv in muxterm_dict.items():
        if ti in newtermdict: print("Step7: Warning: repeated terms (add mux section): ", ti)
        newtermdict[ti] = tv


    for design, bindlist in enumerate(designbindlist_list):
        for bi, bv in bindlist:
            newbinddict[bi] = bv

    for bi, bv in muxbind_dict.items():
        newbinddict[bi] = bv

        # for scope, sig in signals.items(): #in TERMs, the format is [scope: signals]
        #     # TODO: Ho chi incorrect, fix it after working on bind tree
        #     # (6a) if the signal is multi-bit one, we change it to two signal based on the following analysis
        #     #           multi_signal_again <= multi_signal * multi_signal
        #     #           multi_signal <= single_signal
        #     #
        #     #       which will be changed to
        #     #           multi_signal_again_MUX <= multi_signal * multi_signal
        #     #           multi_signal_MUX <= single_signal
        #     # "multi_signal_MUXED" will be used as input of mux, and multi_signal will be output of mux
        #     if str(sig) in sigdiffStr_Refmax :
        #
        #         if sigdiffStr_Refmax[str(sig)][design] != 0:
        #             #del signals[scope]
        #             cpySigIdxMux = scope
        #             cpySigMux = signals[scope]
        #
        #         else:
        #             cpySigIdxMux = copy.deepcopy(scope)
        #             #cpySigIdxMux.scopechain[-1].scopename = cpySigIdxMux.scopechain[-1].scopename + "_mux" + str(design)
        #
        #             #Type: dataflow.Term
        #             #add new term
        #             cpySigMux = copy.deepcopy(signals[scope])
        #
        #         cpySigIdxMux.scopechain[-1].scopename = cpySigIdxMux.scopechain[-1].scopename + "_mux" + str(design)
        #         cpySigMux.name = cpySigIdxMux
        #
        #         print(cpySigMux.termtype)
        #         if signaltype.isInput(cpySigMux.termtype):
        #             cpySigMux.termtype.remove('Input')
        #         elif signaltype.isInout(cpySigMux.termtype):
        #             cpySigMux.termtype.remove('Inout')
        #         elif signaltype.isOutput(cpySigMux.termtype):
        #             cpySigMux.termtype.remove('Output')
        #
        #         signals[cpySigIdxMux] = cpySigMux
        #
        #         #need to change to original one as well :D
        #         if signaltype.isReg(signals[scope].termtype):
        #             signals[scope].termtype.remove('Reg')
        #             signals[scope].termtype.add('Wire')
        #
        #         if signaltype.isRegArray(signals[scope].termtype):
        #             signals[scope].termtype.remove('RegArray')
        #             signals[scope].termtype.add('WireArray')


    """
    for design, signals in enumerate(designterm_list):
        for si, sv in signals.items():
            print(design, sv, sv.termtype)
        #for itm in signals.items():
            #print(type(itm[0]))
    for signali, signalv in muxterm_dict.items():
        print(signali, signalv, signalv.termtype)



    for ti, tv in newtermdict.items():
        print("Final :), ", ti, tv)


    for bi, bv in newbinddict.items():
        for bsv in bv:
            print("Final :), ", bi, bsv.tostr())

    """

    optimizer = VerilogDataflowOptimizer(newtermdict, newbinddict)
    optimizer.resolveConstant()

    resolved_terms = optimizer.getResolvedTerms()
    resolved_binddict = optimizer.getResolvedBinddict()
    constlist = optimizer.getConstlist()

    codegen = VerilogCodeGenerator(options.topmodule, newtermdict, newbinddict,
                                   resolved_terms, resolved_binddict, constlist)

    codegen.set_clock_info(options.clockname, options.clockedge)
    codegen.set_reset_info(options.resetname, options.resetedge)

    code = codegen.generateCode(options.searchtarget)

    f = open(options.outputfile, 'w')
    f.write(code)
    f.close()







    """

    directives = analyzer.get_directives()
    print('Directive:')
    for dr in sorted(directives, key=lambda x:str(x)):
        print(dr)

    instances = analyzer.getInstances()
    print('Instance:')
    print(instances)
    for module, instname in sorted(instances, key=lambda x:str(x[1])):
        print((module, instname))

    if options.nobind:
        print('Signal:')
        signals = analyzer.getSignals()
        for sig in signals:
            print(sig)

        print('Const:')
        consts = analyzer.getConsts()
        for con in consts:
            print(con)

    else:
        terms = analyzer.getTerms()
        print('Term:')
        print(terms)

        for tk, tv in sorted(terms.items(), key=lambda x:str(x[0])):
            print(tv.tostr())
   
        binddict = analyzer.getBinddict()
        print('Bind:')
        for bk, bv in sorted(binddict.items(), key=lambda x:str(x[0])):
            #print( bv[0])
            for bvi in bv:
                print(bvi.tostr())


        print('Signal:')
        signals = analyzer.getSignals()
        print(signals)
        for sig in signals:
            print(sig)

        print('Const:')
        consts = analyzer.getConsts()
        for con in consts:
            print(con)

    """

if __name__ == '__main__':
    main()
