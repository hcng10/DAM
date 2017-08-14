from __future__ import absolute_import
from __future__ import print_function
import sys
import os
import re
import copy

from optparse import OptionParser

import pyverilog.utils.version
import pyverilog.utils.signaltype as signaltype
from pyverilog.dataflow.dataflow_analyzer import VerilogDataflowAnalyzer
from pyverilog.dataflow.optimizer import VerilogDataflowOptimizer

mux_binddest_static_list = ('d0', 'q', 'sel')
mux_rn = '_rn0_q'
#mux_signalin_list = ['z_mux']
#mux_signalout = 'z'




mux_verilogtemplate = ""

design_bindlist_list = []
design_bindMuxinfodict = None




def chgMuxBindScope(lowlevelsigname, dinbool, muxforSig, muxbindStr_head_dict, muxbindStr_tree_dict, scope_addtotree, bi, q=None):
    muxhead_binddest = muxbindStr_head_dict[muxforSig]

    # (3c-1) modify the scopechain first, which is the key in the MUX binddest dictionary
    # it should also automatically change the first MUX_binddest TREE node
    if q is None:
        muxhead_binddest.scopechain = muxhead_binddest.scopechain[-2:]
    elif q == True:
        muxhead_binddest.scopechain = muxhead_binddest.scopechain[-1:]
        muxhead_binddest.scopechain[-1].scopename = lowlevelsigname
        #

    for binddests_scope in reversed(bi.scopechain[:-1]):
        scopename = copy.deepcopy(binddests_scope)
        muxhead_binddest.scopechain.insert(0, scopename)


    # (3d) if dinbool is true, then we need to change back the original name
    din_repeatedstr = ''
    if dinbool:
        for e in scope_addtotree:
            din_repeatedstr = din_repeatedstr + e.scopename + '_'

    # (3e) navigate among the values inside MUX_binddest, assign the scope chain to the terminal
    muxtree_binddest = muxbindStr_tree_dict[muxforSig]
    for muxtree_binddest_e in muxtree_binddest:
        muxtree_binddest_e.muxModify(scope_addtotree, dinbool, din_repeatedstr)



def chgMuxTermScope(lowlevelsigname, muxforSig, muxtermStr_ind_dict, muxtermStr_val_dict, scope_addtotree, bi, q=None, sigStr_Type=None):
    mux_term = muxtermStr_ind_dict[muxforSig]

    # (3c-2) modify the scopechain first, which is the key in the MUX term dictionary
    # it should also automatically change the val

    if q is None:
        mux_term.scopechain = mux_term.scopechain[-2:]
    elif q == True:
        mux_term.scopechain = mux_term.scopechain[-1:]

        if lowlevelsigname!=None: mux_term.scopechain[-1].scopename = lowlevelsigname

    # hack: special care for sel
    if mux_term.scopechain[0].scopename == 'sel':
        mux_term.scopechain.insert(0, bi.scopechain[0])
    else:

        for binddests_scope in reversed(bi.scopechain[:-1]):
            scopename = copy.deepcopy(binddests_scope)
            mux_term.scopechain.insert(0, scopename)

    #fix the io/ wire type
    if sigStr_Type != None and str(mux_term) in sigStr_Type:
        for se in sigStr_Type[str(mux_term)]:
            muxtermStr_val_dict[muxforSig].termtype.add(se)




def createMuxVerilogTemplate(design_num, sigdiffStr_Refmax, sigdiffScope_Maxbit, postMCSfixing):
    print(mux_verilogtemplate)
    mux_file = open(mux_verilogtemplate, 'w+')

    mux_file.write("`timescale 1ns / 1ps\n\n")

    #macro for defing bit width
    mux_file.write('`define MUX_SEL_WIDTH   %d \n' % ((design_num - 1).bit_length()))

    #macro for mux input & output
    for sstr, smax in sigdiffScope_Maxbit.items():
        sstr_nodot = sstr.replace('.', '_')

        mux_file.write('`define MUX_%s_I_WIDTH   %s \n' % (sstr_nodot, smax))
        mux_file.write('`define MUX_%s_O_WIDTH   %s \n' % (sstr_nodot, smax))

    #macro for mux
    mux_file.write('\n`define muxcase(caseNum, din) \\\n')
    mux_file.write('caseNum: q = din;\n')

    """---------------------------------------------------------------------------------------------O(signals*design)"""
    for sstr, sbitdiff in sigdiffStr_Refmax.items():
        sstr_nodot = sstr.replace('.', '_')

        mux_file.write('module mux_%s(\n' % (sstr_nodot))
        mux_file.write('    input [`MUX_SEL_WIDTH - 1:0] sel,\n')
        for i in range(0, design_num):
            mux_file.write('    input [`MUX_%s_I_WIDTH - 1:0] d%d,\n' % (sstr_nodot, i))
        mux_file.write('    output reg [`MUX_%s_O_WIDTH - 1:0] q);\n' % (sstr_nodot))


        mux_file.write('    always @ (*) begin \n        case(sel)\n')
        for i in range(0, design_num):
            mux_file.write('            `muxcase(`MUX_SEL_WIDTH\'d%d, d%d)\n' % (i, i))
        mux_file.write('        endcase\n   end\n')

        mux_file.write('endmodule\n')


    #statement for instantiate the muxes
    mux_file.write('module mux_template(sel);\n')
    mux_file.write('    input [`MUX_SEL_WIDTH-1:0] sel;\n')

    #assume that, when dealing with multi-bit, the corresponding tree is common across designs
    #therefore viewing the Muxinfo in the first design is already good
    #if postMCSfixing != None and postMCSfixing == True:
        #design_bindMuxinfodict = None
    #else:
        #design_bindMuxinfodict = design_bindMuxinfodict_list[0]
        #print(">>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>", design_bindMuxinfodict)


    """---------------------------------------------------------------------------------------------O(signals*design)"""
    for sstr, sbitdiff in sigdiffStr_Refmax.items():
        sstr_nodot = sstr.replace('.', '_')

        #There can be cases where the multi-bit has never been assigned
        if (postMCSfixing == None or postMCSfixing == False) and sstr not in design_bindMuxinfodict: continue
        #bindMuxinfo = design_bindMuxinfodict[sstr]

        if (postMCSfixing != None and postMCSfixing == True) or \
                    (design_bindMuxinfodict[sstr].termMultiNum > 0 and design_bindMuxinfodict[sstr].hasCmp):
            mux_file.write('    wire [`MUX_%s_O_WIDTH - 1:0] %s;\n' % (sstr_nodot, sstr_nodot))

            # create wires
            for i in range(0, design_num):
                mux_file.write('    wire [`MUX_%s_I_WIDTH - 1:0] %s_mux%d;\n' % (sstr_nodot, sstr_nodot, i))

            # create the mux
            mux_file.write('    mux_%s mux_%s(.sel(sel), ' % (sstr_nodot, sstr_nodot))
            for i in range(0, design_num):
                if sbitdiff[i] == 0 or (sbitdiff[i] + sigdiffScope_Maxbit[sstr]) == 0:
                    wrsignal = '%s_mux%d' % (sstr_nodot, i)  # sbitdiff[i] is a negative number
                else:
                    wrsignal = '{%d\'d0, %s_mux%d[%d:0]}' % (
                    0 - sbitdiff[i], sstr_nodot, i, sigdiffScope_Maxbit[sstr] + sbitdiff[i] - 1)

                mux_file.write('.d%d(%s), ' % (i, wrsignal))

            mux_file.write('.q(%s));\n' % (sstr_nodot))

        else:
            sstr_nodot_mux = sstr_nodot + '_mux'

            #create wires
            mux_file.write('    wire [`MUX_%s_O_WIDTH - 1:0] %s;\n' %(sstr_nodot, sstr_nodot))
            mux_file.write('    wire [`MUX_%s_I_WIDTH - 1:0] %s;\n' %(sstr_nodot, sstr_nodot_mux))

            #create the mux
            mux_file.write('    mux_%s mux_%s(.sel(sel), ' % (sstr_nodot, sstr_nodot))
            for i in range(0, design_num):
                if sbitdiff[i] == 0:
                    wrsignal = '%s_mux' %(sstr_nodot)  #sbitdiff[i] is a negative number
                elif  (sbitdiff[i] + sigdiffScope_Maxbit[sstr]) == 0:
                    wrsignal = ''
                else:
                    wrsignal = '{%d\'d0, %s_mux[%d:0]}' %(0-sbitdiff[i], sstr_nodot, sigdiffScope_Maxbit[sstr]+sbitdiff[i]-1)

                mux_file.write('.d%d(%s), ' %(i, wrsignal))

            mux_file.write('.q(%s));\n' %(sstr_nodot))



        mux_file.write('\n')


    mux_file.write('endmodule\n')


    mux_file.close()



def generateMuxDataStruct(prefixName, design_num, designbindlist_list, bindMuxinfodict, sigdiffStr_Refmax, sigdiffScope_Maxbit, postMCSfixing = None):
    global mux_verilogtemplate
    mux_verilogtemplate = prefixName + "__mux.v"

    global design_bindlist_list
    design_bindlist_list = designbindlist_list

    global design_bindMuxinfodict
    design_bindMuxinfodict = bindMuxinfodict

    createMuxVerilogTemplate(design_num, sigdiffStr_Refmax, sigdiffScope_Maxbit, postMCSfixing)


def scopeToStr_MuxDataStruct(muxterm_dict, muxbind_dict, reNewDict=None):
    muxbindStr_head_dict = {}
    muxbindStr_tree_dict = {}
    muxbind_dict_new = {}
    for bi, bv in muxbind_dict.items():
        muxbindStr_head_dict[str(bi)] = bi
        muxbindStr_tree_dict[str(bi)] = bv
        if reNewDict:
            muxbind_dict_new[bi] = bv


    muxtermStr_ind_dict = {}
    muxtermStr_val_dict = {}
    muxterm_dict_new = {}
    for ti, tv in muxterm_dict.items():
        muxtermStr_ind_dict[str(ti)] = ti
        muxtermStr_val_dict[str(ti)] = tv
        if reNewDict:
            muxterm_dict_new[ti] = tv

    if reNewDict:
        muxbind_dict = muxbind_dict_new
        muxterm_dict = muxterm_dict_new
        return [muxterm_dict, muxbind_dict, muxtermStr_ind_dict, muxtermStr_val_dict, muxbindStr_head_dict, muxbindStr_tree_dict]
    else:
        return [muxtermStr_ind_dict, muxtermStr_val_dict, muxbindStr_head_dict, muxbindStr_tree_dict]


def generateMuxTemplate(prefixName, design_num, bind_list, bindMuxinfo, sigdiffStr_Refmax, sigdiffScope_Maxbit, sigStr_Type):
    #mux_file = open(prefixName + "_mux.v", "w")


    for sig in sigdiffStr_Refmax:
        print(sig)

    analyzer = VerilogDataflowAnalyzer([prefixName + "__mux.v"], "mux_template",
                                           noreorder=False,
                                           nobind=False,
                                           preprocess_include=[],
                                           preprocess_define=[])
    analyzer.generate()
    muxterm_dict = analyzer.getTerms()
    muxbind_dict = analyzer.getBinddict()


    # print("\nBind list for mux")
    # muxbind_list = sorted(muxbind_dict.items(), key=lambda x: str(x[0]))
    # for bi, bv in muxbind_list:
    #       #print("bi>>>>>>>>>>>>>>>>", bi)
    #       for bve in bv:
    #           print(bve.tostr())

    """1st: This is a hack, convert the binddest object from scope to str
        to support faster search later"""
    [muxtermStr_ind_dict, muxtermStr_val_dict, muxbindStr_head_dict, muxbindStr_tree_dict] = \
                                                            scopeToStr_MuxDataStruct(muxterm_dict, muxbind_dict)

    mux_binddest_list = []

    """ 2nd: create the list of dest for replacement in mux_binddest_dict
    """
    for mux_binddest_str in mux_binddest_static_list:
        mux_binddest_list.append(mux_binddest_str)

        # that depends on the number of designs, which determine the number of inputs to mux
        m = re.search("\d", mux_binddest_str)
        if m:
            digit_loc = m.start()
            for digi in range(1, design_num):
                mux_binddest_str2 = mux_binddest_str.replace('0', str(digi))
                mux_binddest_list.append(mux_binddest_str2)

    for i in range(0, len(sigdiffStr_Refmax)*design_num):
        mux_rn2 = mux_rn.replace('0', str(i))
        mux_binddest_list.append(mux_rn2)

    """ 3rd: start from bind tree perspective, help the signal to create mux (term will be changed with another function)
        Note the signal name in the mux file is composed of <level0>_<level1>_<old_sig_name>, so we need to convert it
        back to old_sig_name for terms and binddest
    """
    for bi, bv in bind_list:
        bi_str = str(bi)
        muxIdfy = bindMuxinfo[bi_str]

        if muxIdfy.headmux == True:
            # entire bind tree multi-bit
            #if muxIdfy.termNum == muxIdfy.termMultiNum:
            signame = bi_str
            signame = signame.replace('.', '_')

            lowlevelsigname = bi.scopechain[-1].scopename

            #natvigate the bind tree of mux, change the content correspondingly

            #(3a)place the scopes from NORMAL binddest for the MUX_binddest tree use,
            #   based on the scope of the signals in the USER DESIGNS
            scope_addtotree = []
            for binddests_scope in reversed(bi.scopechain[:-1]):
                # this doesn't do deep copy
                scope_addtotree.insert(0, binddests_scope)


            # (3b)take care of the head in MUX_bind_dest
            #       it always has the format mux_template.mux_<original signal name>.<_rn0_q or d0.....>
            for mux_binddest_str in mux_binddest_list:
                muxforSig = 'mux_template.mux_' + signame + '.' + mux_binddest_str
                dinbool = mux_binddest_str[0] == 'd' #hack; determine if it is an input
                # (3c) (3d) in the function
                # check the case for rnq first
                if muxforSig in muxbindStr_head_dict:
                    chgMuxBindScope(None, dinbool, muxforSig, muxbindStr_head_dict, muxbindStr_tree_dict, scope_addtotree, bi)

                    chgMuxTermScope(None, muxforSig, muxtermStr_ind_dict, muxtermStr_val_dict, scope_addtotree, bi)



            # (3e) Hack: hardcode the final case, which is the output signal for the mux
            muxforSig = 'mux_template.' + signame #+ '.' + mux_signalout
            chgMuxBindScope(lowlevelsigname, False, muxforSig, muxbindStr_head_dict, muxbindStr_tree_dict, scope_addtotree, bi, q=True)

            chgMuxTermScope(lowlevelsigname, muxforSig, muxtermStr_ind_dict, muxtermStr_val_dict, scope_addtotree, bi,  q=True, sigStr_Type=sigStr_Type)


            # (3f) Handling the unhandle signal name, usually they are on the top level
            #   case 1: tree common, but with multi-bit and compare
            if muxIdfy.termMultiNum > 0 and muxIdfy.hasCmp:
                for d in range(0, design_num):
                    muxforSig = 'mux_template.' + signame + '_mux' + str(d)
                    chgMuxTermScope(lowlevelsigname+ '_mux' + str(d), muxforSig, muxtermStr_ind_dict, muxtermStr_val_dict, scope_addtotree, bi, q=True)

            #   case 2: tree common, but with multi-bit and no compare
            #   case 3: entire tree common but no multi-bit
            else:
                muxforSig = 'mux_template.' + signame + '_mux'
                chgMuxTermScope(lowlevelsigname + '_mux', muxforSig, muxtermStr_ind_dict, muxtermStr_val_dict, \
                                scope_addtotree, bi, q=True)

            #Hack: the top sel signal
            muxforSig = 'mux_template.sel'
            chgMuxTermScope(None, muxforSig, muxtermStr_ind_dict, muxtermStr_val_dict, scope_addtotree, bi, q=True)

    muxbind_list = sorted(muxbind_dict.items(), key=lambda x: str(x[0]))

    # for bi, bv in muxbind_list:
    #     #print("bi>>>>>>>>>>>>>>>>", bi)
    #     for bve in bv:
    #         print(bve.tostr())

    for ti, tv in muxterm_dict.items():
        print(">>>>>>>>>>>>>>>>>>>>>>>>>>>>>>",ti, tv.termtype)


    """ 4nd: return a correct data structure to enable fast deletion in vmerge
    """
    [muxterm_dict, muxbind_dict, muxtermStr_ind_dict, muxtermStr_val_dict, muxbindStr_head_dict, muxbindStr_tree_dict] = \
                                                            scopeToStr_MuxDataStruct(muxterm_dict, muxbind_dict, reNewDict=True)


    return [muxterm_dict, muxtermStr_ind_dict, muxtermStr_val_dict, muxbind_dict, muxbindStr_head_dict, muxbindStr_tree_dict]

    # print("\nBind list for mux")
    # muxbind_list = sorted(muxbind_dict.items(), key=lambda x: str(x[0]))
    # for bi, bv in muxbind_list:
    #        #print("bi>>>>>>>>>>>>>>>>", bi)
    #       for bve in bv:
    #           print(bve.tostr())
    #
    #  #mux_file.close()
    # terms = analyzer.getTerms()
    # print(">>>>>>>>>>>>>>>>>>>>>>>>>>>>>>", terms)

def deleteMuxTerm(ti, muxtermStr_ind_dict, muxterm_dict):

    if str(ti) in muxtermStr_ind_dict:
        print("mux signal deleted: ", str(ti))
        termscopetodelete = muxtermStr_ind_dict[str(ti)]
        del muxterm_dict[termscopetodelete]