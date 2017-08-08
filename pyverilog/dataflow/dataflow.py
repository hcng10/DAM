#-------------------------------------------------------------------------------
# dataflow.py
#
# Basic classes of Data flow nodes
#
# Copyright (C) 2013, Shinya Takamaeda-Yamazaki
# License: Apache 2.0
# Contributor: ryosuke fukatani
#-------------------------------------------------------------------------------
from __future__ import absolute_import
from __future__ import print_function
import sys
import os
import re
import copy

################################################################################
dfnodelist = ('DFIntConst', 'DFFloatConst', 'DFStringConst',
              'DFEvalValue', 'DFUndefined', 'DFHighImpedance',
              'DFTerminal',
              'DFBranch', 'DFOperator', 'DFPartselect', 'DFPointer',
              'DFConcat', 'DFDelay', 'DFSyscall')

# predemux = 1
# prodemux = 2
#


def printIndent(s, indent=4):
    print((' ' * indent) + s)

def generateWalkTree(offset=1):
    base_indent = 4
    printIndent('def walkTree(tree):', base_indent*(0+offset))
    for df in dfnodelist:
        printIndent('if isinstance(tree, %s):' % df, base_indent * (1+offset))
        printIndent('pass', base_indent * (2+offset))

if __name__ == '__main__':
    generateWalkTree()
    exit()

################################################################################
import pyverilog.utils.verror as verror
import pyverilog.utils.util as util
import pyverilog.utils.signaltype as signaltype
import pyverilog.utils.op2mark as op2mark
from pyverilog.dataflow.vmerge_var import *

################################################################################
class DFNode(object):
    attr_names = ()
    def __init__(self): pass
    def __repr__(self): pass
    def tostr(self): pass
    def tocode(self, dest='dest'): return self.__repr__()
    def tolabel(self): return self.__repr__()
    def children(self):
        nodelist = []
        return tuple(nodelist)
    def __eq__(self, other):
        if type(self) != type(other): return False
        return False
    def __ne__(self, other):
        return not self.__eq__(other)
    def __hash__(self):
        return id(self)
    def toPrint(self): pass
    # finding mcs and corresponding code generation
    def IDNeighbour(self,  preNode, headScope, design_i, designtermdict_list, preNode_level=None, info_str=None): pass
    def IDFirstM_AB(self, designB_i, termo_set, designMCSOutput_list, designM_AB_initial_list, designF_A_list): pass
    def MCS_NodeCmp(self, DFNode_i): pass

    # preNode: refers to the head, or the starting point of the conditional in branch
    def traverse(self, preNode, sigDiff, muxIdfy, options, info_dict, info_op = None, info_str=None):pass
    # This function is only used in mux structure, and only the terminal needs to be changed :)
    def muxModify(self, newScopeName_list, dinbool=None, din_repeatedstr=None): pass
    def fixpartsel(self, headScope, fixpartsel_termdict, fixpartsel_binddict, assign_analyzer, partsel_cnt_packaslist): pass

    # preNode: refers to the node right above >< sorry it is a bit confusing
    def bindDestVModify(self, options, casenum, designnum, concatanalyzer, partselectanalyzer, sigdiffStr_Refmax, sigdiffStr_Maxbit, preNode = None, info_op = None): pass
    def concatBindDestVModify(self, originalterminal, maxbit, bitdiff, preNode = None): pass
    def partselectBindDestVModify(self, originalterminal, maxbit, bitdiff, preNode = None): pass
    def rmvOldConnectNewNode(self, originalterminal, newtree): pass
    def bindDestBrModify(self, options, bindBrIdfyDict, designnum, partselectanalyzer, sigdiffStr_Refmax, sigdiffStr_Maxbit, isCond, preNode = None, info_op = None): pass

    def findGraphSizeGoDeep(self, n, designnum, mcshead_list, arg_head, arg_matcheddesign_i_list, arg_node_cnt, arg_match_cnt):

        [ret_case, dummy_head, ret_matcheddesign_i_list, ret_node_cnt, ret_match_cnt] = \
            n.findGraphSize(designnum, mcshead_list, arg_head, arg_matcheddesign_i_list, arg_node_cnt, arg_match_cnt)

        if ret_case == MCS_NODE_SAME:
            arg_matcheddesign_i_list = ret_matcheddesign_i_list
            arg_node_cnt = ret_node_cnt
            arg_match_cnt = ret_match_cnt

        return [arg_matcheddesign_i_list, arg_node_cnt, arg_match_cnt]

    """
    findGraphSize: determine the size of the mcs
    pre:
        designnum: the number of design
        subgraphhead_list: a list that contains all the nodes that are ID as head during the finding process
        current_head: the head of the graph that I am trying to extend
        prenode_matcheddesign: a list that contains True/ False, where the position indicates the design number
        node_cnt: the number of node spotted in the same subgraph so far
    post:
        ret_head: A: current_head: means this node is part of the prenode mcs
                  B: None: current node cannot be matched anywhere
                  C: self: I form a new head

    """

    def findGraphSize(self, designnum, mcshead_list, current_head, prenode_matcheddesign_i_list, mcsnode_cnt, mcsmatch_cnt):


        update_mcsnode_cnt = mcsnode_cnt

        pre_selfnode_matcheddesign_i_list = []
        selfnode_matcheddesign_i_list = []

        update_mcsmatch_cnt_same = mcsmatch_cnt
        update_mcsmatch_cnt_new = 0

        # Perform Analysis first
        for designmatched_i in range(0, designnum):

            # case 1: prenode and self are in the same sub-tree
            if current_head != None:  # first you got to ensure that u are part of the mcs to be investigated
                if prenode_matcheddesign_i_list[designmatched_i] == True \
                        and designmatched_i in self.designAtoB_dict:

                    update_mcsnode_cnt = mcsnode_cnt + 1
                    update_mcsmatch_cnt_same = update_mcsmatch_cnt_same + 1 # matched cnt is based on subtree context

                    pre_selfnode_matcheddesign_i_list.append(True)
                else:
                    pre_selfnode_matcheddesign_i_list.append(False)

            if designmatched_i in self.designAtoB_dict and designmatched_i != self.selfdesignnum:

                update_mcsmatch_cnt_new = update_mcsmatch_cnt_new + 1
                selfnode_matcheddesign_i_list.append(True)
            else:
                selfnode_matcheddesign_i_list.append(False)


        # Mark the case first, then handle afterwards
        if update_mcsnode_cnt == mcsnode_cnt:  # case 0: prenode and self are not in the same subgraph

            if self.designAtoB_dict:  # case 0A: check if this node can be matched
                ret_case = MCS_NODE_HEAD
            else:  # case 0B: cannot even be matched, self is an individual node
                ret_case = MCS_NODE_UNMATCHED
        else:  # case 1: prenode and self are in the same sub-tree
            ret_case = MCS_NODE_SAME


        # Make proper action based on the case
        if ret_case == MCS_NODE_HEAD:
            mcshead_list.append(self)

            ret_head = self
            ret_matcheddesign_i_list = selfnode_matcheddesign_i_list
            ret_mcsnode_cnt = 1
            ret_mcsmatch_cnt = update_mcsmatch_cnt_new

            self.graphsize = 1
            self.matchsize = update_mcsmatch_cnt_new
            self.matcheddesign = selfnode_matcheddesign_i_list
            self.mcs_breakpt = True

        elif ret_case == MCS_NODE_UNMATCHED:

            ret_head = None
            ret_matcheddesign_i_list = None
            ret_mcsnode_cnt = 0
            ret_mcsmatch_cnt = 0
            self.mcs_breakpt = True

        else:

            ret_head = current_head
            ret_matcheddesign_i_list = pre_selfnode_matcheddesign_i_list
            ret_mcsnode_cnt = update_mcsnode_cnt
            ret_mcsmatch_cnt = update_mcsmatch_cnt_same

            current_head.graphsize = update_mcsnode_cnt
            current_head.matchsize = update_mcsmatch_cnt_same
            current_head.matcheddesign = pre_selfnode_matcheddesign_i_list
            self.mcs_breakpt = False

        return [ret_case, ret_head, ret_matcheddesign_i_list, ret_mcsnode_cnt, ret_mcsmatch_cnt]


    def MCSBindGenSplitHead(self, new_node, old_node): pass


    def MCSsplitNode(self, MCSsig_cnt, MCScommonbinddict, designtermdict_list, MCScommontermdict, MCSassign_analyzer):

        MCSassign_copied = copy.deepcopy(MCSassign_analyzer.getBinddict())
        self_Scopechain = copy.deepcopy(self.headScope)

        for ti, tv in MCSassign_analyzer.getTerms().items():
            if ti.scopechain[-1].scopename == 'o':
                tv_copied = copy.deepcopy(tv)

                tv_copied.name.scopechain[-1].scopename = "partsel_sig" + str(MCSsig_cnt)
                tv_copied.name.scopechain = self_Scopechain[:-1] + [tv_copied.name.scopechain[-1]]

                designtermdict_list[self.selfdesignnum][tv_copied.name] = tv_copied

                tv_copied.msb.value = str(self.term_width)
                tv_copied.lsb.value = str(0)



        for mcsa_i, mcsa_v in MCSassign_copied.items():
            # use the terminal to replace me

            terminal_node = mcsa_v[0].tree
            terminal_node.name.scopechain[-1].scopename = "mcs_sig" + str(MCSsig_cnt)
            terminal_node.name.scopechain = self_Scopechain[:-1] + [terminal_node.name.scopechain[-1]]
            mcsa_v[0].tree = self

            mcsa_i.scopechain[-1].scopename = "mcs_sig" + str(MCSsig_cnt)
            mcsa_i.scopechain = self_Scopechain[:-1] + [mcsa_i.scopechain[-1]]

            MCScommonbinddict[mcsa_i] = mcsa_v

            self.parent.MCSBindGenSplitHead(terminal_node, self)
            self.parent = mcsa_v[0]

            terminal_node.matchedcnt = self.matchedcnt

        self.MCSbindgen_nodesplit = True


    def MCSBindGen(self, headnode, MCSsig_cnt, designbinddict_list, MCScommonbinddict, MCSbinddict_list, designtermdict_list, MCScommontermdict, MCSassign_analyzer, M_B_bool=None): pass


    def MCSBindGenDFNode(self, headnode, MCSsig_cnt, designbinddict_list, MCScommonbinddict, MCSbinddict_list, designtermdict_list, MCScommontermdict, MCSassign_analyzer, M_B_bool=None):

        if self.MCSbindgen_visited == True:
            print("Terminal already visited.....", end=' ')
            self.toPrint()
            return [MCSsig_cnt, False, None, None]


        # No need to go down bcos if it is a mcs, it will be visited again
        if M_B_bool != None or (self.mcs_breakpt == True and id(self) != id(headnode)):
            if M_B_bool != None:
                print("--> M_B_bool: Terminal got to be redirected.....",  "mcs_sig" + str(MCSsig_cnt), ".....", end=' ')
            else:
                print("Terminal got to be redirected.....", end=' ')
            self.toPrint()

            MCSassign_copied = copy.deepcopy(MCSassign_analyzer.getBinddict())

            self_Scopechain = copy.deepcopy(self.headScope)

            #put the new term in the list of its design
            for ti, tv in  MCSassign_analyzer.getTerms().items():
                if ti.scopechain[-1].scopename == 'o':
                    tv_copied = copy.deepcopy(tv)

                    tv_copied.name.scopechain[-1].scopename = "partsel_sig" + str(MCSsig_cnt)
                    tv_copied.name.scopechain = self_Scopechain[:-1] + [tv_copied.name.scopechain[-1]]

                    designtermdict_list[self.selfdesignnum][tv_copied.name] = tv_copied
                    #fix the width

                    tv_copied.msb.value = str(self.term_width)
                    tv_copied.lsb.value = str(0)


            # since there is one element in the list, the loop is going to iterate once only
            for mcsa_i, mcsa_v in MCSassign_copied.items():
                #print(mcsa_v[0].tree, mcsa_v[0].dest, mcsa_i.scopechain, self_Scopechain)

                # use the terminal to replace me
                terminal_node = mcsa_v[0].tree
                terminal_node.name.scopechain[-1].scopename = "mcs_sig" + str(MCSsig_cnt)
                terminal_node.name.scopechain = self_Scopechain[:-1] + [terminal_node.name.scopechain[-1]]
                mcsa_v[0].tree = self

                # make it point to binddest (changing mcsa_i.scopechain will also change mcsa_v[0].dest)
                mcsa_i.scopechain[-1].scopename = "mcs_sig" + str(MCSsig_cnt)
                mcsa_i.scopechain = self_Scopechain[:-1] + [mcsa_i.scopechain[-1]]

                # print(mcsa_v[0].tree, mcsa_v[0].dest, mcsa_i.scopechain, self.parentstr)


                MCSbinddict_list[self.selfdesignnum][mcsa_i] = mcsa_v
                self.parent = mcsa_v[0]

                MCSsig_cnt = MCSsig_cnt + 1

            return [MCSsig_cnt, True, terminal_node]

        # I am the head case, or it is in the same MCS
        else:
            # jmp to the corresponding node in the other sub-tree
            print("Terminal stays the same.....", end=' ')
            self.toPrint()

            self.MCSbindgen_visited = True

            for di, dv in enumerate(headnode.matcheddesign):
                if dv == True:
                    self.designAtoB_dict[di].MCSbindgen_visited = True

            return [MCSsig_cnt, self.mcs_breakpt, None]


    def MCSBindGenDFNotTerminal(self, headnode, MCSsig_cnt, designbinddict_list, MCScommonbinddict, MCSbinddict_list, designtermdict_list, MCScommontermdict, MCSassign_analyzer, \
                                children_list, childrenstr_list, children_can_diff, M_B_bool=None):
        #if M_B_bool != None:
        if self.MCSbindgen_visited == True:
            print("Node already visited.....", end=' ')
            self.toPrint()
            return [MCSsig_cnt, False, None, None]


        if M_B_bool != None or (self.mcs_breakpt == True and id(self) != id(headnode)):
            if M_B_bool != None:
                print("---> M_B_bool: Node got to be redirected.....",  "mcs_sig" + str(MCSsig_cnt) , ".....",end=' ')
            else:
                print("Node got to be redirected.....", end=' ')
            self.toPrint()

            MCSassign_copied = copy.deepcopy(MCSassign_analyzer.getBinddict())

            self_Scopechain = copy.deepcopy(self.headScope)

            for ti, tv in  MCSassign_analyzer.getTerms().items():
                if ti.scopechain[-1].scopename == 'o':
                    tv_copied = copy.deepcopy(tv)

                    tv_copied.name.scopechain[-1].scopename = "partsel_sig" + str(MCSsig_cnt)
                    tv_copied.name.scopechain = self_Scopechain[:-1] + [tv_copied.name.scopechain[-1]]

                    designtermdict_list[self.selfdesignnum][tv_copied.name] = tv_copied

                    tv_copied.msb.value = str(self.term_width)
                    tv_copied.lsb.value = str(0)


            for mcsa_i, mcsa_v in MCSassign_copied.items():
                #print(mcsa_v[0].tree, mcsa_v[0].dest, mcsa_i.scopechain, self_Scopechain)

                # use the terminal to replace me
                terminal_node = mcsa_v[0].tree
                terminal_node.name.scopechain[-1].scopename = "mcs_sig" + str(MCSsig_cnt)
                terminal_node.name.scopechain = self_Scopechain[:-1] + [terminal_node.name.scopechain[-1]]
                mcsa_v[0].tree = self

                # make it point to binddest (changing mcsa_i.scopechain will also change mcsa_v[0].dest)
                mcsa_i.scopechain[-1].scopename = "mcs_sig" + str(MCSsig_cnt)
                mcsa_i.scopechain = self_Scopechain[:-1] + [mcsa_i.scopechain[-1]]

                # print(mcsa_v[0].tree, mcsa_v[0].dest, mcsa_i.scopechain, self.parentstr)

                MCSbinddict_list[self.selfdesignnum][mcsa_i] = mcsa_v
                self.parent = mcsa_v[0]

                MCSsig_cnt = MCSsig_cnt + 1

            self.MCSbindgen_nodesplit = True

            return [MCSsig_cnt, True, terminal_node, None]

        else:
            print("Node stays the same.....", end=' ')
            self.toPrint()

            #case that I am a head node, that means I have to split and form new tree
            if id(self) == id(headnode):
                #if type(self.parent) != Bind:

                if self.MCSbindgen_nodesplit == False:
                    print(".....I got to split to node.....", end=' ')
                    self.toPrint()

                    self.MCSsplitNode(MCSsig_cnt, MCScommonbinddict, designtermdict_list, MCScommontermdict, MCSassign_analyzer)

                    for di, dv in enumerate(headnode.matcheddesign):
                        if dv == True:
                            if self.designAtoB_dict[di].MCSbindgen_nodesplit == True:
                                sys.stderr.write(str(type(self)) + ": my neighbour should not have formed new head by himself, exit!")
                                exit()

                            else:
                                self.designAtoB_dict[di].MCSsplitNode(MCSsig_cnt, MCScommonbinddict, designtermdict_list, MCScommontermdict, MCSassign_analyzer)


                    MCSsig_cnt = MCSsig_cnt + 1



            # jmp to the corresponding node in the other sub-tree
            self.MCSbindgen_visited = True
            for di, dv in enumerate(headnode.matcheddesign):
                if dv == True:
                    self.designAtoB_dict[di].MCSbindgen_visited = True

            ret_children_list = []
            for childi, child in enumerate(children_list):
                if child is not None:
                    [ret_MCSsig_cnt, ret_mcs_breakpt, ret_terminal_node] = \
                        child.MCSBindGen(headnode, MCSsig_cnt, designbinddict_list, MCScommonbinddict, MCSbinddict_list, designtermdict_list, MCScommontermdict, MCSassign_analyzer, M_B_bool)


                    if children_can_diff == True:
                        # You got to jump to other node to fix other nodes as well
                        if ret_mcs_breakpt == True:
                            for di, dv in enumerate(headnode.matcheddesign):
                                if dv == True:
                                    self.designAtoB_dict[di].MCSBindGen_B(MCSsig_cnt, designbinddict_list, MCScommonbinddict, MCSbinddict_list, designtermdict_list, MCScommontermdict, MCSassign_analyzer,
                                                                          childrenstr_list[childi])

                            #MCSsig_cnt = ret_MCSsig_cnt

                            ret_children_list.append(ret_terminal_node)

                        else:
                            ret_children_list.append(child)

                        MCSsig_cnt = ret_MCSsig_cnt
                    else:
                        if ret_mcs_breakpt == True:
                            sys.stderr.write(type(self), ": Children are not the same between designs, exit!")
                            exit()


            return [MCSsig_cnt, self.mcs_breakpt, None, ret_children_list]

    def codeToValue(self, instr):
        str_list = re.split('(\+|\-|\*|\(|\))', instr)

        out_str = ''
        for s in str_list:
            if '\'b' in s:
                out_str += str(int(s[s.index('\'b') + 2:], 2))
            else:
                out_str += s
        if out_str.isdigit():
            return int(out_str)
        else:
            return eval(out_str)


class DFTerminal(DFNode):
    attr_names = ('name',)
    def __init__(self, name):
        self.neighbour = []
        self.name = name
    def __repr__(self):
        ret = ''
        for n in self.name:
            ret += str(n) + '.'
        return ret[:-1]
    def tostr(self):
        ret = '(Terminal '
        for n in self.name:
            ret += str(n) + '.'
        return ret[0:-1] + ')'
    def tocode(self, dest='dest'):
        #ret = ''
        #for n in self.name:
        #    ret += n.tocode() + '__'
        #return ret[:-2]
        return self.name.tocode()
    def tolabel(self):
        return self.tocode()
    def children(self):
        nodelist = []
        return tuple(nodelist)
    def __eq__(self, other):
        if type(self) != type(other): return False
        return self.name == other.name
    def __hash__(self):
        return hash(self.name)

    def toPrint(self):
        ret = ''
        for n in self.name:
            ret += str(n) + '.'
        print(str(self.selfdesignnum), id(self), ret[:-1])

    def IDNeighbour(self, preNode, headScope, design_i, designtermdict_list, preNode_level=None, info_str=None):
        self.selfdesignnum = design_i
        self.node_level = preNode_level + 1

        self.neighbour.append(preNode)
        self.parent = preNode
        self.parentstr = info_str
        self.selfstr = self.tostr()

        self.designAtoB_dict ={}
        self.designBtoA_dict = {}

        self.matchedcnt = 0

        self.headScope = headScope
        self.MCSbindgen_nodesplit = False
        self.MCSbindgen_visited = False
        
        term = designtermdict_list[self.selfdesignnum][self.name]
        self.term_width = self.codeToValue(term.msb.tocode()) - self.codeToValue(term.lsb.tocode()) + 1

        return self.term_width




    def IDFirstM_AB(self, designB_i, termo_set, designMCSOutput_list, designM_AB_initial_list, designF_A_list):

        # This is important, the starting of the MCS is here
        if str(self.name) in termo_set:
            designMCSOutput_list[designB_i].insertNode(self)
            self.output_matched = -1

            if designB_i > 0:
                # iterate every previous design to get the same output ports as starting point
                for designA_i in range(0, designB_i):

                    matchedoutput = designMCSOutput_list[designA_i].matchNode_Output(self, designB_i)
                    if matchedoutput is not None:
                        matchedoutput.output_matched = designB_i # Mark it so that when a node has the same property
                                                                 # wouldn't be matched again

                        M_AB = designM_AB_initial_list[designB_i - 1]
                        F_A = designF_A_list[designB_i - 1]

                        M_AB.insertNode_M_AtoB(matchedoutput, self)
                        if M_AB.getNode_M_B(self) == None:
                            M_AB.insertNode_M_B(self)

                        F_A.insertNode(matchedoutput)

                        matchedoutput.designAtoB_dict[designB_i] = self
                        self.designBtoA_dict[designA_i] = matchedoutput

                        matchedoutput.matchedcnt = matchedoutput.matchedcnt + 1
                        self.matchedcnt = self.matchedcnt + 1

                        print("~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~", designB_i, designA_i, self.name, ":::",  self.parentstr, matchedoutput.designAtoB_dict)




    def MCS_NodeCmp(self, DFNode_i):
        if type(self) == type(DFNode_i) and str(self.name.scopechain) == str(DFNode_i.name.scopechain) and self.parentstr == DFNode_i.parentstr:
            return True
        else:
            return False

    def MCSBindGen(self, headnode, MCSsig_cnt, designbinddict_list, MCScommonbinddict, MCSbinddict_list, designtermdict_list, MCScommontermdict, MCSassign_analyzer, M_B_bool=None):

        return self.MCSBindGenDFNode( headnode, MCSsig_cnt, designbinddict_list, MCScommonbinddict, MCSbinddict_list, \
                                                                               designtermdict_list, MCScommontermdict, MCSassign_analyzer, M_B_bool)



    def fixpartsel(self, headScope, fixpartsel_termdict, fixpartsel_binddict, assign_analyzer, partsel_cnt_packaslist):
        term = fixpartsel_termdict[self.name]
        return self.codeToValue(term.msb.tocode()) - self.codeToValue(term.lsb.tocode()) + 1


    def traverse(self, preNode, sigDiff, muxIdfy, options, info_dict, info_op = None, info_str=None):
        self.preNode = preNode
        if not (self.name[-1].scopename == options.clockname or self.name[-1].scopename == options.resetname):
            # statement inside branch is excluded
            if not info_str:
                muxIdfy.termNum = muxIdfy.termNum +1

                if str(self.name) in sigDiff:
                    # if info_op == None:
                    #     self.demux = prodemux
                    # elif info_op ==  'opcmp':
                    #     self.demux = predemux #######hcng: 20Jan maybe dont need this

                    muxIdfy.termMultiNum = muxIdfy.termMultiNum + 1

            elif 'branch' in info_str:
                #brMuxIdfy = info_dict['branch'][preNode]

                brIdfy = muxIdfy.brIdfyDict[preNode]

                brIdfy.termNum = brIdfy.termNum + 1

                if str(self.name) in sigDiff:
                    brIdfy.termMultiNum = brIdfy.termMultiNum + 1


        ret =  str(self.matchedcnt)+'(Terminal '
        for n in self.name:
            ret += str(n) + '.'
        return ret[0:-1] + ')'

    def muxModify(self, newScopeName_list, dinbool=None, din_repeatedstr=None):
        #check if "mux_template" exists in the name
        e0_scopechain = self.name.scopechain[0]
        if e0_scopechain.scopename == "mux_template":
            self.name.scopechain.remove(e0_scopechain)

            scopename_cpy = copy.deepcopy(newScopeName_list)

            if dinbool and self.name.scopechain[-1].scopename.startswith(din_repeatedstr):
                self.name.scopechain[-1].scopename = self.name.scopechain[-1].scopename[len(din_repeatedstr):]

            if self.name.scopechain[-1].scopename == 'sel':
                self.name.scopechain = scopename_cpy[:1] + self.name.scopechain[-1:]

            else:
                self.name.scopechain = scopename_cpy + self.name.scopechain[-2:]

    """
    This function is called to modify the signal name in the bind tree, or even WORSE
    change the structure of bind tree

    Changes are required when Head: multi, Children: some-multi
    To support this change, we bring in the concat-bind-structure, deep copy it
    then change the concat-bind-structure based on the signal names in designs
    (function 'concatBindDestVModify' <- is used to support that)

    Then once it is changed, it has to be connected to the design bindtree
    (function 'rmvOldConnectNewNode' <- is used to support that)

    Last, but not the least, we need to change the binddest to support the uncommon part in different designs :(
    """
    def bindDestVModify(self, casenum, options, designnum, concatanalyzer, partselectanalyzer, sigdiffStr_Refmax,\
                        sigdiffStr_Maxbit, preNode = None, info_op = None):

        # if there is clk or rst, basically u can ignore it
        if (self.name[-1].scopename == options.clockname or self.name[-1].scopename == options.resetname):
            return

        tname = str(self.name)

        if casenum == BIND_CHILD_WITH_MULTI:

            if tname in sigdiffStr_Refmax:
                #handle it when we know we have comparision operator
                if info_op == "opCmp" and \
                                sigdiffStr_Refmax[tname][designnum] != 0 and type(preNode) != DFPartselect:

                    curbitdiff = sigdiffStr_Refmax[tname][designnum]
                    maxbit = sigdiffStr_Maxbit[tname]

                    partselectbinddest_dict = copy.deepcopy(partselectanalyzer.getBinddict())
                    for bi, bv in partselectbinddest_dict.items():
                        for bve in bv:
                            # change the binddest structure of concat based on the signal
                            bve.partselectBindDestVModify(self, maxbit, curbitdiff, preNode)


        elif casenum == BIND_DESIGN_DIFF:
            self.name.scopechain[-1].scopename = self.name.scopechain[-1].scopename + str(designnum)



    def concatBindDestVModify(self, originalterminal, maxbit=None, bitdiff=None):
        self.name = copy.deepcopy(originalterminal.name)

    def partselectBindDestVModify(self, originalterminal, maxbit=None, bitdiff=None):
        self.name = copy.deepcopy(originalterminal.name)


    def bindDestBrModify(self, options, bindBrIdfyDict, designnum, partselectanalyzer, sigdiffStr_Refmax, \
                         sigdiffStr_Maxbit, isCond, preNode = None, info_op = None):

        # handle when u know u are in the condition, or not clk or rst
        if (self.name[-1].scopename == options.clockname or self.name[-1].scopename == options.resetname):
            return

        if isCond == True:
            tname = str(self.name)

            if tname in sigdiffStr_Refmax:

                # you got to do partsel when u have Cmp
                if info_op and 'opCmp' in info_op and \
                                sigdiffStr_Refmax[tname][designnum] != 0 and type(preNode) != DFPartselect:

                    curbitdiff = sigdiffStr_Refmax[tname][designnum]
                    maxbit = sigdiffStr_Maxbit[tname]

                    partselectbinddest_dict = copy.deepcopy(partselectanalyzer.getBinddict())
                    for bi, bv in partselectbinddest_dict.items():
                        for bve in bv:
                            # change the binddest structure of concat based on the signal
                            bve.partselectBindDestVModify(self, maxbit, curbitdiff, preNode)
            # else:
            #     self.name.scopechain[-1].scopename = self.name.scopechain[-1].scopename + str(designnum)



class DFConstant(DFNode):
    attr_names = ('value',)
    def __init__(self, value):
        self.value = value
        self.neighbour = []
    def __repr__(self):
        return str(self.value)
    def tostr(self):
        ret = '(Constant ' + str(self.value) + ')'
        return ret
    def children(self):
        nodelist = []
        return tuple(nodelist)
    def eval(self):
        return None
    def __eq__(self, other):
        if type(self) != type(other): return False
        return self.value == other.value
    def __hash__(self):
        return hash(self.value)

    def toPrint(self):
        print(str(self.selfdesignnum), id(self), self.parentstr, str(self.value))

    def IDNeighbour(self,  preNode, headScope, design_i, designtermdict_list, preNode_level=None, info_str=None):
        self.selfdesignnum = design_i
        self.node_level = preNode_level + 1

        self.neighbour.append(preNode)
        self.parent = preNode
        self.parentstr = info_str
        self.selfstr = self.tostr()

        self.designAtoB_dict ={}
        self.designBtoA_dict = {}
        self.matchedcnt = 0

        self.headScope = headScope
        self.MCSbindgen_nodesplit = False
        self.MCSbindgen_visited = False

        self.term_width = int(self.value).bit_length()
        if self.term_width == 0: self.term_width = 1

        return self.term_width

    def MCS_NodeCmp(self, DFNode_i):
        if type(self) == type(DFNode_i) and self.value == DFNode_i.value and self.parentstr == DFNode_i.parentstr:
            return True
        else:
            return False

    def MCSBindGen(self, headnode, MCSsig_cnt, designbinddict_list, MCScommonbinddict, MCSbinddict_list, designtermdict_list, MCScommontermdict, MCSassign_analyzer, M_B_bool=None):
        return self.MCSBindGenDFNode( headnode, MCSsig_cnt, designbinddict_list, MCScommonbinddict, MCSbinddict_list, \
                                                                                designtermdict_list, MCScommontermdict, MCSassign_analyzer, M_B_bool)


    def fixpartsel(self, headScope, fixpartsel_termdict, fixpartsel_binddict, assign_analyzer, partsel_cnt_packaslist):
        ret = int(self.value).bit_length()
        if ret == 0: ret = 1

        return ret

    def traverse(self, preNode, sigDiff, muxIdfy, options, info_dict, info_op = None, info_str=None):
        self.preNode = preNode

        if not info_str:
            muxIdfy.constantNum = muxIdfy.constantNum + 1
        elif 'branch' in info_str:
            brIdfy = muxIdfy.brIdfyDict[preNode]
            brIdfy.constantNum = brIdfy.constantNum + 1


        ret =  str(self.matchedcnt)+'(Constant ' + str(self.value) + ')'
        return ret

    def muxModify(self, newScopeName_list, dinbool=None, din_repeatedstr=None):
        return

class DFIntConst(DFConstant):
    def __init__(self, value):
        self.value = value
        self.neighbour = []
    def tostr(self):
        ret = '(IntConst ' + str(self.value) + ')'
        return ret
    def eval(self):
        targ = self.value.replace('_','')
        signed = False
        match = re.search(r'[Ss](.+)', targ)
        if match is not None:
            signed = True
        match = re.search(r'[Hh](.+)', targ)
        if match is not None:
            return int(match.group(1), 16)
        match = re.search(r'[Dd](.+)', targ)
        if match is not None:
            return int(match.group(1), 10)
        match = re.search(r'[Oo](.+)', targ)
        if match is not None:
            return int(match.group(1), 8)
        match = re.search(r'[Bb](.+)', targ)
        if match is not None:
            return int(match.group(1), 2)
        return int(targ, 10)
    def width(self):
        targ = self.value.replace('_','')
        match = re.search(r'(.+)\'[Hh].+', targ)
        if match is not None:
            return int(match.group(1), 10)
        match = re.search(r'(.+)\'[Dd].+', targ)
        if match is not None:
            return int(match.group(1), 10)
        match = re.search(r'(.+)\'[Oo].+', targ)
        if match is not None:
            return int(match.group(1), 10)
        match = re.search(r'(.+)\'[Bb].+', targ)
        if match is not None:
            return int(match.group(1), 10)
        return 32

    def toPrint(self):
        print(str(self.selfdesignnum), id(self), self.parentstr, str(self.value))

    def IDNeighbour(self,  preNode, headScope, design_i, designtermdict_list, preNode_level=None, info_str=None):
        self.selfdesignnum = design_i
        self.node_level = preNode_level + 1

        self.neighbour.append(preNode)
        self.parent = preNode
        self.parentstr = info_str
        self.selfstr = self.tostr()

        self.designAtoB_dict ={}
        self.designBtoA_dict = {}
        self.matchedcnt = 0

        self.headScope = headScope
        self.MCSbindgen_nodesplit = False
        self.MCSbindgen_visited = False

        self.term_width = int(self.value).bit_length()
        if self.term_width == 0: self.term_width = 1

        return self.term_width

    def MCS_NodeCmp(self, DFNode_i):
        if type(self) == type(DFNode_i) and self.value == DFNode_i.value and self.parentstr == DFNode_i.parentstr:
            return True
        else:
            return False

    def MCSBindGen(self, headnode, MCSsig_cnt, designbinddict_list, MCScommonbinddict, MCSbinddict_list, designtermdict_list, MCScommontermdict, MCSassign_analyzer, M_B_bool=None):
        return self.MCSBindGenDFNode( headnode, MCSsig_cnt, designbinddict_list, MCScommonbinddict, MCSbinddict_list, \
                                                                               designtermdict_list, MCScommontermdict, MCSassign_analyzer, M_B_bool)


    def fixpartsel(self, headScope, fixpartsel_termdict, fixpartsel_binddict, assign_analyzer, partsel_cnt_packaslist):
        if self.value.isdigit():
            ret = int(self.value).bit_length()
            if ret == 0: ret = 1
        else:
            ret = self.width()

        return ret


    def traverse(self, preNode, sigDiff, muxIdfy, options, info_dict, info_op = None, info_str=None):
        self.preNode = preNode

        if not info_str and \
                info_str != 'lsb' and info_str != 'msb' and \
                self.value != 0:
            muxIdfy.constantNum = muxIdfy.constantNum + 1

        elif 'branch' in info_str and self.value != 0:

            brIdfy = muxIdfy.brIdfyDict[preNode]
            brIdfy.constantNum = brIdfy.constantNum + 1

        ret =  str(self.matchedcnt)+'(IntConst ' + str(self.value) + ')'
        return ret
    #it gets here bcos of the case msb or bcos of the lsb concated
    def concatBindDestVModify(self, originalterminal, maxbit, bitdiff):
        #hack again, we use the bitwidth to identify the case
        if self.value == "1'b1":
            self.value = str(0 - bitdiff) + '\'b0'
        elif self.value == "30":
            self.value = str(maxbit + bitdiff - 1)

    # it gets here bcos of the case msb or bcos of the lsb partselect
    def partselectBindDestVModify(self, originalterminal, maxbit, bitdiff):
        if self.value == "28": self.value = str(maxbit + bitdiff - 1)


class DFFloatConst(DFConstant):
    def __init__(self, value):
        self.value = value
        self.neighbour = []
    def tostr(self):
        ret = '(FloatConst ' + str(self.value) + ')'
        return ret
    def eval(self):
        return float(self.value)

    def toPrint(self):
        print(str(self.selfdesignnum), id(self), self.parentstr, str(self.value))

    def IDNeighbour(self,  preNode, headScope, design_i, designtermdict_list, preNode_level=None, info_str=None):
        self.selfdesignnum = design_i
        self.node_level = preNode_level + 1

        self.neighbour.append(preNode)
        self.parent = preNode
        self.parentstr = info_str
        self.selfstr = self.tostr()
        self.matchedcnt = 0

        self.designAtoB_dict ={}
        self.designBtoA_dict = {}

        self.headScope = headScope
        self.MCSbindgen_nodesplit = False
        self.MCSbindgen_visited = False

        self.term_width = 32

        return self.term_width

    def MCS_NodeCmp(self, DFNode_i):
        if type(self) == type(DFNode_i) and self.value == self.value and self.parentstr == DFNode_i.parentstr:
            return True
        else:
            return False

    def MCSBindGen(self, headnode, MCSsig_cnt, designbinddict_list, MCScommonbinddict, MCSbinddict_list, designtermdict_list, MCScommontermdict, MCSassign_analyzer, M_B_bool=None):
        return self.MCSBindGenDFNode( headnode, MCSsig_cnt, designbinddict_list, MCScommonbinddict, MCSbinddict_list,\
                                                                               designtermdict_list, MCScommontermdict, MCSassign_analyzer, M_B_bool)


    def fixpartsel(self, headScope, fixpartsel_termdict, fixpartsel_binddict, assign_analyzer, partsel_cnt_packaslist):

        #TODO: This is Hack
        return 32

    def traverse(self, preNode, sigDiff, muxIdfy, options, info_dict, info_op = None, info_str=None):
        self.preNode = preNode

        if not info_str:
            muxIdfy.constantNum = muxIdfy.constantNum + 1

        elif 'branch' in info_str:
            brIdfy = muxIdfy.brIdfyDict[preNode]
            brIdfy.constantNum = brIdfy.constantNum + 1

        ret =  str(self.matchedcnt)+'(FloatConst ' + str(self.value) + ')'
        return ret

class DFStringConst(DFConstant):
    def __init__(self, value):
        self.value = value
        neighbour = []
    def tostr(self):
        ret = '(StringConst ' + str(self.value) + ')'
        return ret
    def eval(self):
        return self.value

    def toPrint(self):
        print(str(self.selfdesignnum), id(self), self.parentstr, str(self.value))

    def IDNeighbour(self,  preNode, headScope, design_i, designtermdict_list, preNode_level = None, info_str = None):
        self.selfdesignnum = design_i
        self.node_level = preNode_level + 1

        self.neighbour.append(preNode)
        self.parent = preNode
        self.parentstr = info_str
        self.selfstr = self.tostr()

        self.designAtoB_dict ={}
        self.designBtoA_dict = {}
        self.matchedcnt = 0

        self.headScope = headScope
        self.MCSbindgen_nodesplit = False
        self.MCSbindgen_visited = False

        self.term_width = int(self.value).bit_length()
        if self.term_width == 0: self.term_width = 1

        return self.term_width


    def MCS_NodeCmp(self, DFNode_i):
        if type(self) == type(DFNode_i) and self.value == DFNode_i.value and self.parentstr == DFNode_i.parentstr:
            return True
        else:
            return False

    def MCSBindGen(self, headnode, MCSsig_cnt, designbinddict_list, MCScommonbinddict, MCSbinddict_list, designtermdict_list, MCScommontermdict, MCSassign_analyzer, M_B_bool=None):
        return self.MCSBindGenDFNode(headnode, MCSsig_cnt, designbinddict_list, MCScommonbinddict, MCSbinddict_list, designtermdict_list, MCScommontermdict, MCSassign_analyzer, M_B_bool)


    def fixpartsel(self, headScope, fixpartsel_termdict, fixpartsel_binddict, assign_analyzer, partsel_cnt_packaslist):

        ret = int(self.value).bit_length()
        if ret == 0: ret = 1
        return ret


    def traverse(self, preNode, sigDiff, muxIdfy, options, info_dict, info_op = None, info_str=None):
        self.preNode = preNode

        ret =  str(self.matchedcnt)+'(StringConst ' + str(self.value) + ')'
        return ret

################################################################################
class DFNotTerminal(DFNode): #pass
    def findGraphSize(self, designnum, mcshead_list, current_head, prenode_matcheddesign_i_list, mcsnode_cnt, mcsmatch_cnt):
        return super(DFNotTerminal, self).findGraphSize(designnum, mcshead_list, current_head, prenode_matcheddesign_i_list,
                                          mcsnode_cnt, mcsmatch_cnt)

class DFOperator(DFNotTerminal):
    attr_names = ('operator',)
    def __init__(self, nextnodes, operator):
        self.nextnodes = nextnodes
        self.operator = operator
        self.neighbour = []

        for n in nextnodes:
            if n is None: raise verror.DefinitionError()

    def __repr__(self):
        return self.operator
    def tostr(self):
        ret = '(Operator ' + self.operator
        ret += ' Next:'
        for n in self.nextnodes: ret += n.tostr() + ','
        ret = ret[0:-1] + ')'
        return ret

    def tocode(self, dest='dest'):
        ret = ''
        if len(self.nextnodes) > 1:
            ret += '(' + self.nextnodes[0].tocode(dest)
            ret += op2mark.op2mark(self.operator)
            ret += self.nextnodes[1].tocode(dest) + ')'
        else:
            ret += '(' + op2mark.op2mark(self.operator)
            ret += self.nextnodes[0].tocode(dest) + ')'
        return ret
    def children(self):
        nodelist = []
        if self.nextnodes is not None: nodelist.extend(self.nextnodes)
        return tuple(nodelist)
    def __eq__(self, other):
        if type(self) != type(other): return False
        return self.operator == other.operator and self.nextnodes == other.nextnodes
    def __hash__(self):
        return hash((self.operator, tuple(self.nextnodes)))

    def toPrint(self):
        print(str(self.selfdesignnum), id(self), self.parentstr, "DFOperator", self.operator)

    def IDNeighbour(self,  preNode, headScope, design_i, designtermdict_list, preNode_level=None, info_str=None):
        self.selfdesignnum = design_i
        self.node_level = preNode_level + 1

        self.neighbour.append(preNode)

        self.term_width = 0
        for i, n in enumerate(self.nextnodes):
            self.neighbour.append(n)
            bit = n.IDNeighbour(self, headScope, design_i, designtermdict_list, self.node_level + 1, self.operator + str(i))

            if self.term_width < bit:
                self.term_width = bit

        self.parent = preNode
        self.parentstr = info_str
        self.selfstr = self.operator

        self.designAtoB_dict ={}
        self.designBtoA_dict = {}
        self.matchedcnt = 0

        self.headScope = headScope
        self.MCSbindgen_nodesplit = False
        self.MCSbindgen_visited = False


        if signaltype.isTimes(self.operator):
            self.term_width = self.term_width + bit

        if signaltype.isPlusMinus(self.operator):
            self.term_width = self.term_width +1


        if signaltype.isCompare(self.operator):
            self.term_width = 1

        return self.term_width


    def IDFirstM_AB(self, designB_i, termo_set, designMCSOutput_list, designM_AB_initial_list, designF_A_list):

        for n in self.nextnodes:
            n.IDFirstM_AB(designB_i, termo_set, designMCSOutput_list, designM_AB_initial_list, designF_A_list)

    def MCS_NodeCmp(self, DFNode_i):
        if type(self) == type(DFNode_i) and self.operator == DFNode_i.operator and self.parentstr == DFNode_i.parentstr:
            # TODO: we hack, check all the children number are the same, so that if there are differences, it can be easily replaced
            if len(self.nextnodes) != len(DFNode_i.nextnodes):
                return False
            else:
                #for ni in range(0, len(self.nextnodes)):
                #    if self.nextnodes[ni].selfstr != DFNode.nextnodes[ni].selfstr:
                #        return False

                return True
        else:
            return False

    def findGraphSize(self, designnum, mcshead_list, current_head, prenode_matcheddesign_i_list, mcsnode_cnt, mcsmatch_cnt):

        [self_case, self_head, self_matcheddesign_i_list, self_mcsnode_count, self_mcmatch_count]= \
            super(DFOperator, self).findGraphSize(designnum, mcshead_list, current_head, prenode_matcheddesign_i_list, mcsnode_cnt, mcsmatch_cnt)

        ### using another var to avoid polluting self variable
        arg_head = self_head
        arg_node_cnt = self_mcsnode_count
        arg_match_cnt = self_mcmatch_count

        if self_case == MCS_NODE_UNMATCHED:
            arg_matcheddesign_i_list = []

        elif self_case == MCS_NODE_HEAD or self_case == MCS_NODE_SAME:
            arg_matcheddesign_i_list = copy.copy(self_matcheddesign_i_list)


        ### OKAY now go deeper
        for n in self.nextnodes:
            [arg_matcheddesign_i_list, arg_node_cnt, arg_match_cnt] = \
                self.findGraphSizeGoDeep(n, designnum, mcshead_list, arg_head, arg_matcheddesign_i_list, arg_node_cnt, arg_match_cnt)


        # return var
        if self_case == MCS_NODE_UNMATCHED or self_case == MCS_NODE_HEAD:
            return [self_case, None, None, mcsnode_cnt, mcsmatch_cnt]

        else: # the match list need to be updated by children
            return [self_case, current_head, arg_matcheddesign_i_list, arg_node_cnt, arg_match_cnt]




    def MCSBindGen(self, headnode, MCSsig_cnt, designbinddict_list, MCScommonbinddict, MCSbinddict_list, designtermdict_list, MCScommontermdict, MCSassign_analyzer, M_B_bool=None):

        children_list = list(self.nextnodes)
        childrenstr_list = list(range(len(self.nextnodes)))

        [ret_MCSsig_cnt, ret_mcs_breakpt, ret_terminal_node, ret_children_list] = self.MCSBindGenDFNotTerminal\
            (headnode, MCSsig_cnt, designbinddict_list, MCScommonbinddict, MCSbinddict_list, designtermdict_list, MCScommontermdict, MCSassign_analyzer, children_list, childrenstr_list, True, M_B_bool)

        if ret_children_list != None:
            self.nextnodes = tuple(ret_children_list)

        return [ret_MCSsig_cnt, ret_mcs_breakpt, ret_terminal_node]


    def MCSBindGen_B(self, MCSsig_cnt, designbinddict_list, MCScommonbinddict, MCSbinddict_list, designtermdict_list, MCScommontermdict, MCSassign_analyzer, nextnode_num):

        print("B redirected.....", end=' ')
        self.toPrint()

        nextnodes_list = list(self.nextnodes)

        [MCSsig_cnt, ret_mcs_breakpt, ret_terminal_node] = \
            nextnodes_list[nextnode_num].MCSBindGen(None, MCSsig_cnt, designbinddict_list, MCScommonbinddict, MCSbinddict_list, designtermdict_list, MCScommontermdict, MCSassign_analyzer, True)

        nextnodes_list[nextnode_num] = ret_terminal_node

        self.nextnodes = tuple(nextnodes_list)

    def MCSBindGenSplitHead(self, new_node, old_node):
        nextnodes_list = list(self.nextnodes)

        for nn_i in range(0, len(nextnodes_list)):
            if (nextnodes_list[nn_i]) == id(old_node):
                nextnodes_list[nn_i] = new_node

        self.nextnodes = tuple(nextnodes_list)


    def fixpartsel(self, headScope, fixpartsel_termdict, fixpartsel_binddict, assign_analyzer, partsel_cnt_packaslist):

        max_bit = 0
        for n in self.nextnodes:
            bit = n.fixpartsel(headScope, fixpartsel_termdict, fixpartsel_binddict, assign_analyzer, partsel_cnt_packaslist)
            if max_bit < bit:
                max_bit = bit

            if signaltype.isTimes(self.operator):
                max_bit = max_bit + bit

        if signaltype.isPlusMinus(self.operator):
            max_bit = max_bit +1


        if signaltype.isCompare(self.operator):
            max_bit = 1

        return max_bit



    def traverse(self, preNode, sigDiff, muxIdfy, options, info_dict, info_op = None, info_str=None):
        self.preNode = preNode

        ret = '(Operator ' + self.operator
        ret += ' Next:'

        if signaltype.isCompare(self.operator):

            if info_str and 'branch' in info_str:
                brIdfy = muxIdfy.brIdfyDict[preNode]
                brIdfy.hasCmp = True

            else:
                muxIdfy.hasCmp = True
        else:
            info_op = None

        for n in self.nextnodes: ret += n.traverse(preNode, sigDiff, muxIdfy, options, info_dict, info_op, info_str) + ','
        ret =  str(self.matchedcnt)+ret[0:-1] + ')'
        return ret

    def muxModify(self, newScopeName_list, dinbool=None, din_repeatedstr=None):
        for n in self.nextnodes:
            n.muxModify(newScopeName_list, dinbool, din_repeatedstr)


    def bindDestVModify(self, casenum, options, designnum, concatanalyzer, partselectanalyzer, sigdiffStr_Refmax, sigdiffStr_Maxbit, preNode = None, info_op = None):
        if signaltype.isCompare(self.operator): info_op = "opCmp"
        for n in self.nextnodes:
            n.bindDestVModify(casenum, options, designnum, concatanalyzer, partselectanalyzer, sigdiffStr_Refmax, sigdiffStr_Maxbit, self, info_op)

    def rmvOldConnectNewNode(self, originalterminal, newtree):

        for i, n in enumerate(self.nextnodes):
            if n == originalterminal:
                self.nextnodes = self.nextnodes[:i] + (newtree, ) + self.nextnodes[i+1:]
                break

    def bindDestBrModify(self, options, bindBrIdfyDict, designnum, partselectanalyzer, sigdiffStr_Refmax, sigdiffStr_Maxbit, isCond, preNode = None, info_op=None):
        if signaltype.isCompare(self.operator): info_op = 'opCmp'
        for n in self.nextnodes:
            n.bindDestBrModify(options, bindBrIdfyDict, designnum, partselectanalyzer, sigdiffStr_Refmax, sigdiffStr_Maxbit, isCond, self, info_op)


class DFPartselect(DFNotTerminal):
    attr_names = ()
    def __init__(self, var, msb, lsb):
        self.var = var
        self.msb = msb
        self.lsb = lsb
        self.neighbour = []

    def __repr__(self):
        return 'PartSelect'
    def tostr(self):
        ret = '(Partselect'
        ret += ' Var:' + self.var.tostr()
        ret += ' MSB:' + self.msb.tostr()
        ret += ' LSB:' + self.lsb.tostr()
        ret += ')'
        return ret

    def tocode(self, dest='dest'):
        ret = self.var.tocode(dest)
        msbcode = self.msb.tocode(dest)
        lsbcode = self.lsb.tocode(dest)
        if msbcode == lsbcode:
            ret += '[' + msbcode + ']'
        else:
            ret += '[' + msbcode
            ret += ':' + lsbcode + ']'
        return ret
    def children(self):
        nodelist = []
        if self.var is not None: nodelist.append(self.var)
        if self.msb is not None: nodelist.append(self.msb)
        if self.lsb is not None: nodelist.append(self.lsb)
        return tuple(nodelist)
    def __eq__(self, other):
        if type(self) != type(other): return False
        return self.var == other.var and self.msb == other.msb and self.lsb == other.lsb
    def __hash__(self):
        return hash((self.var, self.msb, self.lsb))

    def toPrint(self):
        print(str(self.selfdesignnum), id(self), self.parentstr, "DFPartselect", str(self.var))

    def IDNeighbour(self,  preNode, headScope, design_i, designtermdict_list, preNode_level=None, info_str=None):
        self.selfdesignnum = design_i
        self.node_level = preNode_level + 1

        self.neighbour.append(preNode)
        self.neighbour.append(self.var)
        self.neighbour.append(self.msb)
        self.neighbour.append(self.lsb)

        self.var.IDNeighbour(self, headScope, design_i, designtermdict_list, self.node_level + 1, "DFPartselect_var")
        self.msb.IDNeighbour(self, headScope, design_i, designtermdict_list, self.node_level + 1, "DFPartselect_msb")
        self.lsb.IDNeighbour(self, headScope, design_i, designtermdict_list, self.node_level + 1, "DFPartselect_lsb")

        self.parent = preNode
        self.parentstr = info_str
        self.selfstr = 'Partselect'

        self.designAtoB_dict ={}
        self.designBtoA_dict = {}
        self.matchedcnt = 0

        self.headScope = headScope
        self.MCSbindgen_nodesplit = False
        self.MCSbindgen_visited = False

        final_msb = self.codeToValue(self.msb.tocode())
        final_lsb = self.codeToValue(self.lsb.tocode())
        self.term_width =  final_msb - final_lsb + 1

        return self.term_width

    def IDFirstM_AB(self, designB_i, termo_set, designMCSOutput_list, designM_AB_initial_list, designF_A_list):

        self.var.IDFirstM_AB(designB_i, termo_set, designMCSOutput_list, designM_AB_initial_list, designF_A_list)
        self.msb.IDFirstM_AB(designB_i, termo_set, designMCSOutput_list, designM_AB_initial_list, designF_A_list)
        self.lsb.IDFirstM_AB(designB_i, termo_set, designMCSOutput_list, designM_AB_initial_list, designF_A_list)

    def MCS_PartselCmp(self, selfChild, DFChild):



        if isinstance(selfChild, DFTerminal) and isinstance(DFChild, DFTerminal):
            if str(selfChild.name.scopechain) == str(DFChild.name.scopechain):
                return True

        elif isinstance(selfChild, DFOperator) and isinstance(DFChild, DFOperator):
            if selfChild.operator == DFChild.operator:
                return True

        elif isinstance(selfChild, DFConstant) and isinstance(DFChild, DFConstant):
            if selfChild.value == DFChild.value:
                return True

        elif type(selfChild) == type(DFChild):
            if selfChild.value == DFChild.value:
                return True

        return False


    def MCS_NodeCmp(self, DFNode_i):
        # partsel needs special care
        #self.msb.value == DFNode.msb.value and \
        #self.lsb.value == DFNode.lsb.value:

        inital_ret = False
        if type(self) == type(DFNode_i) and self.parentstr == DFNode_i.parentstr:

            ret = self.MCS_PartselCmp(self.var, DFNode_i.var)

            if ret == False:
                return False
            else:
                ret = self.MCS_PartselCmp(self.msb, DFNode_i.msb)

                if ret == False:
                    return False
                else:
                    ret = self.MCS_PartselCmp(self.lsb, DFNode_i.lsb)

                    if ret == False: return False
                    else: return True

        else:
            return False

    def findGraphSize(self, designnum, mcshead_list, current_head, prenode_matcheddesign_i_list, mcsnode_cnt, mcsmatch_cnt):

        [self_case, self_head, self_matcheddesign_i_list, self_mcsnode_count, self_mcmatch_count] = \
            super(DFPartselect, self).findGraphSize(designnum, mcshead_list, current_head, prenode_matcheddesign_i_list,
                                                  mcsnode_cnt, mcsmatch_cnt)

        ### using another var to avoid polluting self variable
        arg_head = self_head
        arg_node_cnt = self_mcsnode_count
        arg_match_cnt = self_mcmatch_count

        if self_case == MCS_NODE_UNMATCHED:
            arg_matcheddesign_i_list = []

        elif self_case == MCS_NODE_HEAD or self_case == MCS_NODE_SAME:
            arg_matcheddesign_i_list = copy.copy(self_matcheddesign_i_list)

        ### OKAY now go deeper
        [arg_matcheddesign_i_list, arg_node_cnt, arg_match_cnt] = \
            self.findGraphSizeGoDeep(self.var, designnum, mcshead_list, arg_head, arg_matcheddesign_i_list, arg_node_cnt, arg_match_cnt)

        [arg_matcheddesign_i_list, arg_node_cnt, arg_match_cnt] = \
            self.findGraphSizeGoDeep(self.msb, designnum, mcshead_list, arg_head, arg_matcheddesign_i_list, arg_node_cnt, arg_match_cnt)

        [arg_matcheddesign_i_list, arg_node_cnt, arg_match_cnt] = \
            self.findGraphSizeGoDeep(self.lsb, designnum, mcshead_list, arg_head, arg_matcheddesign_i_list, arg_node_cnt, arg_match_cnt)

        # return var
        if self_case == MCS_NODE_UNMATCHED or self_case == MCS_NODE_HEAD:
            return [self_case, None, None, mcsnode_cnt, mcsmatch_cnt]

        else:  # the match list need to be updated by children
            return [self_case, current_head, arg_matcheddesign_i_list, arg_node_cnt, arg_match_cnt]


    def MCSBindGen(self, headnode, MCSsig_cnt, designbinddict_list, MCScommonbinddict, MCSbinddict_list, designtermdict_list, MCScommontermdict, MCSassign_analyzer, M_B_bool=None):

        children_list = [self.var, self.msb, self.lsb]
        childrenstr_list = []

        [ret_MCSsig_cnt, ret_mcs_breakpt, ret_terminal_node, ret_children_list] = self.MCSBindGenDFNotTerminal \
            (headnode, MCSsig_cnt, designbinddict_list, MCScommonbinddict, MCSbinddict_list, designtermdict_list, MCScommontermdict, MCSassign_analyzer, children_list, childrenstr_list, False, M_B_bool)


        return [ret_MCSsig_cnt, ret_mcs_breakpt, ret_terminal_node]


    def fixpartsel(self, headScope, fixpartsel_termdict, fixpartsel_binddict, assign_analyzer, partsel_cnt_packaslist):

        bit = self.var.fixpartsel(headScope, fixpartsel_termdict, fixpartsel_binddict, assign_analyzer,
                                  partsel_cnt_packaslist)

        tv_copied = None
        if not isinstance(self.var, DFTerminal):

            self_Scopechain = copy.deepcopy(headScope)

            for ti, tv in  assign_analyzer.getTerms().items():
                if ti.scopechain[-1].scopename == 'o':
                    tv_copied = copy.deepcopy(tv)

                    tv_copied.name.scopechain[-1].scopename = "partsel_sig" + str(partsel_cnt_packaslist[0])
                    tv_copied.name.scopechain = self_Scopechain[:-1] + [tv_copied.name.scopechain[-1]]


                    fixpartsel_termdict[tv_copied.name] = tv_copied




            #gg, need to change it to terminal
            MCSassign_copied = copy.deepcopy(assign_analyzer.getBinddict())

            for mcsa_i, mcsa_v in MCSassign_copied.items():
                # print(mcsa_v[0].tree, mcsa_v[0].dest, mcsa_i.scopechain, self_Scopechain)

                # use the terminal to replace me

                terminal_node = mcsa_v[0].tree
                terminal_node.name.scopechain[-1].scopename = "partsel_sig" + str(partsel_cnt_packaslist[0])
                terminal_node.name.scopechain = self_Scopechain[:-1] + [terminal_node.name.scopechain[-1]]


                mcsa_v[0].tree = self.var

                # make it point to binddest (changing mcsa_i.scopechain will also change mcsa_v[0].dest)
                mcsa_i.scopechain[-1].scopename = "partsel_sig" + str(partsel_cnt_packaslist[0])
                mcsa_i.scopechain = self_Scopechain[:-1] + [mcsa_i.scopechain[-1]]

                # print(mcsa_v[0].tree, mcsa_v[0].dest, mcsa_i.scopechain, self.parentstr)


                fixpartsel_binddict[mcsa_i] = mcsa_v
                self.var = terminal_node

                partsel_cnt_packaslist[0] = partsel_cnt_packaslist[0] + 1


        # self_msb = self.msb.tocode()
        # self_lsb = self.lsb.tocode()
        #
        # if self_msb.isdigit():
        #     final_msb = int(self_msb)
        # else:
        #     final_msb = eval(self_msb)
        #
        # if self_lsb.isdigit():
        #     final_lsb = int(self_lsb)
        # else:
        #     final_lsb = eval(self_lsb)
        final_msb = self.codeToValue(self.msb.tocode())
        final_lsb = self.codeToValue(self.lsb.tocode())


        if bit < final_msb - final_lsb + 1:
            if tv_copied != None: tv_copied.msb.value = str(final_msb - final_lsb + 1)
        elif bit < final_msb:
            if tv_copied != None: tv_copied.msb.value = str(final_msb)
        else:
            if tv_copied != None: tv_copied.msb.value = str(bit - 1)

        return final_msb - final_lsb + 1



    def traverse(self, preNode, sigDiff, muxIdfy, options, info_dict, info_op = None, info_str=None):
        self.preNode = preNode

        ret =  str(self.matchedcnt)+'(Partselect'
        # even for branch, you don't have to go in, bcos the select MSB, LSB will do the trick
        ret += ' Var:' + self.var.traverse(preNode, sigDiff, muxIdfy, options, info_dict, None, info_str)
        ret += ' MSB:' + self.msb.traverse(preNode, sigDiff, muxIdfy, options, info_dict, info_op, 'msb')
        ret += ' LSB:' + self.lsb.traverse(preNode, sigDiff, muxIdfy, options, info_dict, info_op, 'lsb')
        ret += ')'
        return ret

    def muxModify(self, newScopeName_list, dinbool=None, din_repeatedstr=None):
        self.var.muxModify(newScopeName_list, dinbool, din_repeatedstr)
        self.msb.muxModify(newScopeName_list)
        self.lsb.muxModify(newScopeName_list)


    def bindDestVModify(self, casenum, options, designnum, concatanalyzer, partselectanalyzer, sigdiffStr_Refmax, sigdiffStr_Maxbit, preNode = None, info_op = None):
        self.var.bindDestVModify(casenum, options, designnum, concatanalyzer, partselectanalyzer, sigdiffStr_Refmax, sigdiffStr_Maxbit, self, info_op)
        #should be constant in msb and lsb, so no need go traverse?
        #self.msb.bindDestVModify(casenum, designnum, concatanalyzer, sigdiffStr_Refmax, sigdiffStr_Maxbit, self)
        #self.lsb.bindDestVModify(casenum, designnum, concatanalyzer, sigdiffStr_Refmax, sigdiffStr_Maxbit, self)

    def concatBindDestVModify(self, originalterminal, maxbit, bitdiff):
        self.var.concatBindDestVModify(originalterminal, maxbit, bitdiff)
        self.msb.concatBindDestVModify(originalterminal, maxbit, bitdiff)

    def partselectBindDestVModify(self, originalterminal, maxbit, bitdiff, preNode):
        self.var.partselectBindDestVModify(originalterminal, maxbit, bitdiff)
        self.msb.partselectBindDestVModify(originalterminal, maxbit, bitdiff)

        preNode.rmvOldConnectNewNode(originalterminal, self)

    """
    No function 'rmvOldConnectNewNode' here bcos we assume we wouldn't reach here at all
    """

    def bindDestBrModify(self, options, bindBrIdfyDict, designnum, partselectanalyzer, sigdiffStr_Refmax, sigdiffStr_Maxbit, isCond, preNode = None, info_op=None):
        self.var.bindDestBrModify(options, bindBrIdfyDict, designnum, partselectanalyzer, sigdiffStr_Refmax, sigdiffStr_Maxbit, isCond, self, info_op)


class DFPointer(DFNotTerminal):
    attr_names = ()
    def __init__(self, var, ptr):
        self.var = var
        self.ptr = ptr

        self.neighbour = []
    def __repr__(self):
        return 'Pointer'
    def tostr(self):
        ret = '(Pointer'
        ret += ' Var:' + self.var.tostr()
        ret += ' PTR:' + self.ptr.tostr()
        ret += ')'
        return ret

    def tocode(self, dest='dest'):
        ret = self.var.tocode(dest)
        ret += '[' + self.ptr.tocode(dest) + ']'
        return ret
    def children(self):
        nodelist = []
        if self.var is not None: nodelist.append(self.var)
        if self.ptr is not None: nodelist.append(self.ptr)
        return tuple(nodelist)
    def __eq__(self, other):
        if type(self) != type(other): return False
        return self.var == other.var and self.ptr == other.ptr
    def __hash__(self):
        return hash((self.var, self.ptr))

    def toPrint(self):
        print(str(self.selfdesignnum), id(self), self.parentstr, "DFPointer", str(self.var))

    def IDNeighbour(self,  preNode, headScope, design_i, designtermdict_list, preNode_level=None, info_str=None):
        self.selfdesignnum = design_i
        self.node_level = preNode_level + 1

        self.neighbour.append(preNode)
        self.neighbour.append(self.var)
        self.neighbour.append(self.ptr)

        self.term_width = self.var.IDNeighbour(self, headScope, design_i, designtermdict_list, self.node_level + 1, "DFPointer_var")
        self.ptr.IDNeighbour(self, headScope, design_i, designtermdict_list, self.node_level + 1, "DFPointer_ptr")

        self.parent = preNode
        self.parentstr = info_str
        self.selfstr = 'DFPointer'

        self.designAtoB_dict ={}
        self.designBtoA_dict = {}
        self.matchedcnt = 0

        self.headScope = headScope
        self.MCSbindgen_nodesplit = False
        self.MCSbindgen_visited = False

        return self.term_width

    def fixpartsel(self, headScope, fixpartsel_termdict, fixpartsel_binddict, assign_analyzer, partsel_cnt_packaslist):
        bit = self.var.fixpartsel(headScope, fixpartsel_termdict, fixpartsel_binddict, assign_analyzer, partsel_cnt_packaslist)
        self.ptr.fixpartsel(headScope, fixpartsel_termdict, fixpartsel_binddict, assign_analyzer, partsel_cnt_packaslist)

        return bit


    def IDFirstM_AB(self, designB_i, termo_set, designMCSOutput_list, designM_AB_initial_list, designF_A_list):

        self.var.IDFirstM_AB(designB_i, termo_set, designMCSOutput_list, designM_AB_initial_list, designF_A_list)
        self.ptr.IDFirstM_AB(designB_i, termo_set, designMCSOutput_list, designM_AB_initial_list, designF_A_list)

    def MCS_NodeCmp(self, DFNode_i):
        if type(self) == type(DFNode_i) and self.parentstr == DFNode_i.parentstr:
            return True
        else:
            return False

    def findGraphSize(self, designnum, mcshead_list, current_head, prenode_matcheddesign_i_list, mcsnode_cnt, mcsmatch_cnt):

        [self_case, self_head, self_matcheddesign_i_list, self_mcsnode_count, self_mcmatch_count] = \
            super(DFPointer, self).findGraphSize(designnum, mcshead_list, current_head, prenode_matcheddesign_i_list,
                                                  mcsnode_cnt, mcsmatch_cnt)

        ### using another var to avoid polluting self variable
        arg_head = self_head
        arg_node_cnt = self_mcsnode_count
        arg_match_cnt = self_mcmatch_count

        if self_case == MCS_NODE_UNMATCHED:
            arg_matcheddesign_i_list = []

        elif self_case == MCS_NODE_HEAD or self_case == MCS_NODE_SAME:
            arg_matcheddesign_i_list = copy.copy(self_matcheddesign_i_list)

        ### OKAY now go deeper
        [arg_matcheddesign_i_list, arg_node_cnt, arg_match_cnt] = \
            self.findGraphSizeGoDeep(self.var, designnum, mcshead_list, arg_head, arg_matcheddesign_i_list, arg_node_cnt, arg_match_cnt)

        [arg_matcheddesign_i_list, arg_node_cnt, arg_match_cnt] = \
            self.findGraphSizeGoDeep(self.ptr, designnum, mcshead_list, arg_head, arg_matcheddesign_i_list, arg_node_cnt, arg_match_cnt)

        # return var
        if self_case == MCS_NODE_UNMATCHED or self_case == MCS_NODE_HEAD:
            return [self_case, None, None, mcsnode_cnt, mcsmatch_cnt]

        else:  # the match list need to be updated by children
            return [self_case, current_head, arg_matcheddesign_i_list, arg_node_cnt, arg_match_cnt]

    def MCSBindGen(self, headnode, MCSsig_cnt, designbinddict_list, MCScommonbinddict, MCSbinddict_list, designtermdict_list, MCScommontermdict, MCSassign_analyzer, M_B_bool=None):

        children_list = [self.var, self.ptr]
        childrenstr_list = ['var', 'ptr']

        [ret_MCSsig_cnt, ret_mcs_breakpt, ret_terminal_node, ret_children_list] = self.MCSBindGenDFNotTerminal\
            (headnode, MCSsig_cnt, designbinddict_list, MCScommonbinddict, MCSbinddict_list, designtermdict_list, MCScommontermdict, MCSassign_analyzer, children_list, childrenstr_list, True, M_B_bool)

        if ret_children_list != None:
            self.var = ret_children_list[0]
            self.ptr = ret_children_list[1]

        return [ret_MCSsig_cnt, ret_mcs_breakpt, ret_terminal_node]


    def MCSBindGen_B(self, MCSsig_cnt, designbinddict_list, MCScommonbinddict, MCSbinddict_list, designtermdict_list, MCScommontermdict, MCSassign_analyzer, nextnode_str):

        print("B redirected.....", end=' ')
        self.toPrint()

        if nextnode_str == 'var':
            [MCSsig_cnt, ret_mcs_breakpt, ret_terminal_node] = \
                self.var.MCSBindGen(None, MCSsig_cnt, designbinddict_list, MCScommonbinddict, MCSbinddict_list, designtermdict_list, MCScommontermdict, MCSassign_analyzer, True)

            self.var = ret_terminal_node

        elif nextnode_str == 'ptr':
            [MCSsig_cnt, ret_mcs_breakpt, ret_terminal_node] = \
                self.ptr.MCSBindGen(None, MCSsig_cnt, designbinddict_list, MCScommonbinddict, MCSbinddict_list, designtermdict_list, MCScommontermdict, MCSassign_analyzer, True)

            self.ptr = ret_terminal_node


    def MCSBindGenSplitHead(self, new_node, old_node):

        if id(self.var) == id(old_node):
            self.var = new_node

        if id(self.ptr) == id(old_node):
            self.ptr = new_node


    def traverse(self, preNode, sigDiff, muxIdfy, options, info_dict, info_op = None, info_str=None):
        self.preNode = preNode

        ret =  str(self.matchedcnt)+'(Pointer'
        ret += ' Var:' + self.var.traverse(preNode, sigDiff, muxIdfy, options, info_dict, info_op, info_str)
        ret += ' PTR:' + self.ptr.traverse(preNode, sigDiff, muxIdfy, options, info_dict, info_op, info_str)
        ret += ')'
        return ret

    def muxModify(self, newScopeName_list, dinbool=None, din_repeatedstr=None):
        self.var.muxModify(newScopeName_list, dinbool, din_repeatedstr)
        self.ptr.muxModify(newScopeName_list)


    def bindDestVModify(self, casenum, options, designnum, concatanalyzer, partselectanalyzer, sigdiffStr_Refmax, sigdiffStr_Maxbit, preNode = None, info_op = None):
        self.var.bindDestVModify(casenum, options, designnum, concatanalyzer, partselectanalyzer, sigdiffStr_Refmax, sigdiffStr_Maxbit, self, info_op)
        self.ptr.bindDestVModify(casenum, options, designnum, concatanalyzer, partselectanalyzer, sigdiffStr_Refmax, sigdiffStr_Maxbit, self, info_op)

    def rmvOldConnectNewNode(self, originalterminal, newtree):
        if self.var == originalterminal: self.var = newtree
        if self.ptr == originalterminal: self.ptr = newtree


    def bindDestBrModify(self, options, bindBrIdfyDict, designnum, partselectanalyzer, sigdiffStr_Refmax, sigdiffStr_Maxbit, isCond,
                         preNode=None, info_op=None):
        self.var.bindDestBrModify(options, bindBrIdfyDict, designnum, partselectanalyzer, sigdiffStr_Refmax, sigdiffStr_Maxbit, isCond, self, info_op)
        self.ptr.bindDestBrModify(options, bindBrIdfyDict, designnum, partselectanalyzer, sigdiffStr_Refmax, sigdiffStr_Maxbit, isCond, self, info_op)


class DFConcat(DFNotTerminal):
    attr_names = ()
    def __init__(self, nextnodes):
        self.nextnodes = nextnodes
        self.neighbour = []

    def __repr__(self):
        return 'Concat'
    def tostr(self):
        ret = '(Concat'
        ret += ' Next:'
        for n in self.nextnodes: ret += n.tostr() + ','
        ret = ret[0:-1] + ')'
        return ret

    def tocode(self, dest='dest'):
        ret = '{'
        for n in self.nextnodes: ret += n.tocode(dest) + ','
        ret = ret[:-1]
        ret += '}'
        return ret
    def children(self):
        nodelist = []
        if self.nextnodes is not None: nodelist.extend(self.nextnodes)
        return tuple(nodelist)
    def __eq__(self, other):
        if type(self) != type(other): return False
        return self.nextnodes == other.nextnodes
    def __hash__(self):
        return hash(tuple(self.nextnodes))

    def toPrint(self):
        print(str(self.selfdesignnum), id(self), self.parentstr, "DFConcat", self.nextnodes)

    def IDNeighbour(self,  preNode, headScope, design_i, designtermdict_list, preNode_level=None, info_str=None):
        self.selfdesignnum = design_i
        self.node_level = preNode_level + 1

        self.neighbour.append(preNode)

        self.term_width = 0
        for i, n in enumerate(self.nextnodes):
            self.neighbour.append(n)
            bit = n.IDNeighbour(self, headScope, design_i, designtermdict_list, self.node_level + 1, "DFConcat_" + str(i))
            self.term_width = self.term_width + bit

        self.parent = preNode
        self.parentstr = info_str
        self.selfstr = 'DFConcat'

        self.designAtoB_dict ={}
        self.designBtoA_dict = {}
        self.matchedcnt = 0

        self.headScope = headScope
        self.MCSbindgen_nodesplit = False
        self.MCSbindgen_visited = False

        return self.term_width

    def IDFirstM_AB(self, designB_i, termo_set, designMCSOutput_list, designM_AB_initial_list, designF_A_list):

        for n in self.nextnodes:
            n.IDFirstM_AB(designB_i, termo_set, designMCSOutput_list, designM_AB_initial_list, designF_A_list)

    def MCS_NodeCmp(self, DFNode_i):
        if type(self) == type(DFNode_i) and self.parentstr == DFNode_i.parentstr:
            #return True
            # TODO: we hack, check all the children to see if they are also the same
            # concat is different from operators bcos they are hard to combine across tree
            if len(self.nextnodes) != len(DFNode_i.nextnodes):
                return False
            else:
                for ni in range(0, len(self.nextnodes)):
                    if self.nextnodes[ni].selfstr != DFNode_i.nextnodes[ni].selfstr:
                        return False

                return True
        else:
            return False


    def findGraphSize(self, designnum, mcshead_list, current_head, prenode_matcheddesign_i_list, mcsnode_cnt, mcsmatch_cnt):

        [self_case, self_head, self_matcheddesign_i_list, self_mcsnode_count, self_mcmatch_count] = \
            super(DFConcat, self).findGraphSize(designnum, mcshead_list, current_head, prenode_matcheddesign_i_list,
                                                  mcsnode_cnt, mcsmatch_cnt)

        ### using another var to avoid polluting self variable
        arg_head = self_head
        arg_node_cnt = self_mcsnode_count
        arg_match_cnt = self_mcmatch_count

        if self_case == MCS_NODE_UNMATCHED:
            arg_matcheddesign_i_list = []

        elif self_case == MCS_NODE_HEAD or self_case == MCS_NODE_SAME:
            arg_matcheddesign_i_list = copy.copy(self_matcheddesign_i_list)

        ### OKAY now go deeper
        for n in self.nextnodes:
            [arg_matcheddesign_i_list, arg_node_cnt, arg_match_cnt] = \
                self.findGraphSizeGoDeep(n, designnum, mcshead_list, arg_head, arg_matcheddesign_i_list, arg_node_cnt, arg_match_cnt)
        # return var
        if self_case == MCS_NODE_UNMATCHED or self_case == MCS_NODE_HEAD:
            return [self_case, None, None, mcsnode_cnt, mcsmatch_cnt]

        else:  # the match list need to be updated by children
            return [self_case, current_head, arg_matcheddesign_i_list, arg_node_cnt, arg_match_cnt]


    def MCSBindGen(self, headnode, MCSsig_cnt, designbinddict_list, MCScommonbinddict, MCSbinddict_list, designtermdict_list, MCScommontermdict, MCSassign_analyzer, M_B_bool=None):

        children_list = list(self.nextnodes)
        childrenstr_list = []

        [ret_MCSsig_cnt, ret_mcs_breakpt, ret_terminal_node, ret_children_list] = self.MCSBindGenDFNotTerminal \
            (headnode, MCSsig_cnt, designbinddict_list, MCScommonbinddict, MCSbinddict_list, designtermdict_list, MCScommontermdict, MCSassign_analyzer, children_list, childrenstr_list, False, M_B_bool)


        return [ret_MCSsig_cnt, ret_mcs_breakpt, ret_terminal_node]

    def fixpartsel(self, headScope, fixpartsel_termdict, fixpartsel_binddict, assign_analyzer, partsel_cnt_packaslist):
        max_bit = 0
        for n in self.nextnodes:
            bit = n.fixpartsel(headScope, fixpartsel_termdict, fixpartsel_binddict, assign_analyzer, partsel_cnt_packaslist)
            max_bit = max_bit + bit

        return max_bit


    def traverse(self, preNode, sigDiff, muxIdfy, options, info_dict, info_op = None, info_str=None):
        self.preNode = preNode

        ret =  str(self.matchedcnt)+'(Concat'
        ret += ' Next:'
        for n in self.nextnodes: ret += n.traverse(preNode, sigDiff, muxIdfy, options, info_dict, info_op, info_str) + ','
        ret = ret[0:-1] + ')'
        return ret

    def muxModify(self, newScopeName_list, dinbool=None, din_repeatedstr=None):
        for n in self.nextnodes:
            n.muxModify(newScopeName_list, dinbool, din_repeatedstr)

    def bindDestVModify(self, casenum, options, designnum, concatanalyzer, partselectanalyzer, sigdiffStr_Refmax, sigdiffStr_Maxbit, preNode = None, info_op = None):
        for n in self.nextnodes:
            n.bindDestVModify(casenum, options, designnum, concatanalyzer, partselectanalyzer, sigdiffStr_Refmax, sigdiffStr_Maxbit, self, info_op)

    """
    Of course, we must know it is the head of the concat binddest, so we connect here
    """
    def concatBindDestVModify(self, originalterminal, maxbit, bitdiff, preNode):
        for n in self.nextnodes:
            n.concatBindDestVModify(originalterminal, maxbit, bitdiff)
        preNode.rmvOldConnectNewNode(originalterminal, self)


    def rmvOldConnectNewNode(self, originalterminal, newtree):
        for n in self.nextnodes:
            if n == originalterminal:
                self.n = newtree
                break

    def bindDestBrModify(self, options, bindBrIdfyDict, designnum, partselectanalyzer, sigdiffStr_Refmax, sigdiffStr_Maxbit, isCond,  preNode = None, info_op=None):
        for n in self.nextnodes:
            n.bindDestBrModify(options, bindBrIdfyDict, designnum, partselectanalyzer, sigdiffStr_Refmax, sigdiffStr_Maxbit, isCond, self, info_op)


################################################################################
class DFBranch(DFNotTerminal):
    attr_names = ()
    def __init__(self, condnode, truenode, falsenode):
        self.condnode = condnode
        self.truenode = truenode
        self.falsenode = falsenode

        self.neighbour = []

    def __repr__(self):
        return 'Branch'
    def tostr(self):
        ret = '(Branch'
        if self.condnode is not None: ret += ' Cond:' + self.condnode.tostr()
        if self.truenode is not None: ret += ' True:' + self.truenode.tostr()
        if self.falsenode is not None: ret += ' False:'+ self.falsenode.tostr()
        ret += ')'
        return ret

    def tocode(self, dest='dest', always=''):
        if always == 'clockedge': return self._tocode_always(dest, always)
        if always == 'combination': return self._tocode_always(dest, always)
        ret = '('
        if self.condnode is not None: ret += '(' + self.condnode.tocode(dest) + ')'
        ret += '? '
        if self.truenode is not None: ret += self.truenode.tocode(dest)
        else: ret += dest
        ret += " : "
        if self.falsenode is not None: ret += self.falsenode.tocode(dest)
        else: ret += dest
        ret += ")"
        return ret
    def _tocode_always(self, dest='dest', always='clockedge'):
        ret = 'if('
        if self.condnode is not None: ret += self.condnode.tocode(dest)
        ret += ') begin\n'
        if self.truenode is not None:
            if isinstance(self.truenode, DFBranch):
                ret += self.truenode.tocode(dest, always=always)
            elif always == 'clockedge':
                ret += dest + ' <= ' + self.truenode.tocode(dest) + ';\n'
            elif always == 'combination':
                ret += dest + ' = ' + self.truenode.tocode(dest) + ';\n'
        ret += 'end\n'
        if self.falsenode is not None:
            ret += 'else begin\n'
            if isinstance(self.falsenode, DFBranch):
                ret += self.falsenode.tocode(dest, always=always)
            elif always == 'clockedge':
                ret += dest + ' <= ' + self.falsenode.tocode(dest) + ';\n'
            elif always == 'combination':
                ret += dest + ' = ' + self.falsenode.tocode(dest) + ';\n'
            ret += 'end\n'
        return ret
    def children(self):
        nodelist = []
        if self.truenode is not None: nodelist.append(self.truenode)
        if self.condnode is not None: nodelist.append(self.condnode)
        if self.falsenode is not None: nodelist.append(self.falsenode)
        return tuple(nodelist)
    def __eq__(self, other):
        if type(self) != type(other): return False
        return self.condnode == other.condnode and self.truenode == other.truenode and self.falsenode == other.falsenode
    def __hash__(self):
        return hash((self.condnode, self.truenode, self.falsenode))

    def toPrint(self):
        ret = ''
        if self.condnode is not None: ret += ' Cond:'
        if self.truenode is not None: ret += ' True:'
        if self.falsenode is not None: ret += ' False:'
        print(str(self.selfdesignnum), id(self), self.parentstr, "DFBranch", ret)

    def IDNeighbour(self,  preNode, headScope, design_i, designtermdict_list, preNode_level=None, info_str=None):
        self.selfdesignnum = design_i
        self.node_level = preNode_level + 1
        self.term_width = 0

        self.neighbour.append(preNode)
        if self.condnode is not None:
            self.neighbour.append(self.condnode)
            self.condnode.IDNeighbour(self, headScope, design_i, designtermdict_list, self.node_level + 1, "DFBranch_cond")

        if self.truenode is not None:
            self.neighbour.append(self.truenode)
            self.term_width = self.truenode.IDNeighbour(self, headScope, design_i, designtermdict_list, self.node_level + 1, "DFBranch_true")

        if self.falsenode is not None:
            self.neighbour.append(self.falsenode)
            bit = self.falsenode.IDNeighbour(self, headScope, design_i, designtermdict_list, self.node_level + 1, "DFBranch_false")
            if self.term_width < bit: self.term_width = bit

        self.parent = preNode
        self.parentstr = info_str
        self.selfstr = 'DFBranch'

        self.designAtoB_dict ={}
        self.designBtoA_dict = {}
        self.matchedcnt = 0

        self.headScope = headScope
        self.MCSbindgen_nodesplit = False
        self.MCSbindgen_visited = False

        return self.term_width

    def IDFirstM_AB(self, designB_i, termo_set, designMCSOutput_list, designM_AB_initial_list, designF_A_list):

        if self.condnode is not None:
            self.condnode.IDFirstM_AB(designB_i, termo_set, designMCSOutput_list, designM_AB_initial_list, designF_A_list)

        if self.truenode is not None:
            self.truenode.IDFirstM_AB(designB_i, termo_set, designMCSOutput_list, designM_AB_initial_list, designF_A_list)

        if self.falsenode is not None:
            self.falsenode.IDFirstM_AB(designB_i, termo_set, designMCSOutput_list, designM_AB_initial_list, designF_A_list)

    def MCS_NodeCmp(self, DFNode_i):
        if type(self) == type(DFNode_i) and self.parentstr == DFNode_i.parentstr:

            if (self.condnode is None and DFNode_i.condnode is not None) or \
                    (self.condnode is not None and DFNode_i.condnode is None):
                return False

            if (self.truenode is None and DFNode_i.truenode is not None) or \
                    (self.truenode is not None and DFNode_i.truenode is None):
                return False

            if (self.falsenode is None and DFNode_i.falsenode is not None) or \
                    (self.falsenode is not None and DFNode_i.falsenode is None):
                return False

            return True
        else:
            return False


    def findGraphSize(self, designnum, mcshead_list, current_head, prenode_matcheddesign_i_list, mcsnode_cnt, mcsmatch_cnt):

        [self_case, self_head, self_matcheddesign_i_list, self_mcsnode_count, self_mcmatch_count] = \
            super(DFBranch, self).findGraphSize(designnum, mcshead_list, current_head, prenode_matcheddesign_i_list,
                                                  mcsnode_cnt, mcsmatch_cnt)

        ### using another var to avoid polluting self variable
        arg_head = self_head
        arg_node_cnt = self_mcsnode_count
        arg_match_cnt = self_mcmatch_count

        if self_case == MCS_NODE_UNMATCHED:
            arg_matcheddesign_i_list = []

        elif self_case == MCS_NODE_HEAD or self_case == MCS_NODE_SAME:
            arg_matcheddesign_i_list = copy.copy(self_matcheddesign_i_list)

        ### OKAY now go deeper
        [arg_matcheddesign_i_list, arg_node_cnt, arg_match_cnt] = \
            self.findGraphSizeGoDeep(self.condnode, designnum, mcshead_list, arg_head, arg_matcheddesign_i_list, arg_node_cnt, arg_match_cnt)

        if self.truenode is not None:
            [arg_matcheddesign_i_list, arg_node_cnt, arg_match_cnt] = \
                self.findGraphSizeGoDeep(self.truenode, designnum, mcshead_list, arg_head, arg_matcheddesign_i_list, arg_node_cnt, arg_match_cnt)

        if self.falsenode is not None:
            [arg_matcheddesign_i_list, arg_node_cnt, arg_match_cnt] = \
                self.findGraphSizeGoDeep(self.falsenode, designnum, mcshead_list, arg_head, arg_matcheddesign_i_list, arg_node_cnt, arg_match_cnt)

        # return var
        if self_case == MCS_NODE_UNMATCHED or self_case == MCS_NODE_HEAD:
            return [self_case, None, None, mcsnode_cnt, mcsmatch_cnt]

        else:  # the match list need to be updated by children
            return [self_case, current_head, arg_matcheddesign_i_list, arg_node_cnt, arg_match_cnt]



    def MCSBindGen(self, headnode, MCSsig_cnt, designbinddict_list, MCScommonbinddict, MCSbinddict_list, designtermdict_list, MCScommontermdict, MCSassign_analyzer, M_B_bool=None):

        children_list = [self.condnode, self.truenode, self.falsenode]
        childrenstr_list = ['condnode', 'truenode', 'falsenode']

        [ret_MCSsig_cnt, ret_mcs_breakpt, ret_terminal_node, ret_children_list] = self.MCSBindGenDFNotTerminal\
            (headnode, MCSsig_cnt, designbinddict_list, MCScommonbinddict, MCSbinddict_list, designtermdict_list, MCScommontermdict, MCSassign_analyzer, children_list, childrenstr_list, True, M_B_bool)

        if ret_children_list != None:
            ret_i = 0

            if self.condnode is not None:
                self.condnode = ret_children_list[ret_i]
                ret_i = ret_i + 1

            if self.truenode is not None:
                self.truenode = ret_children_list[ret_i]
                ret_i = ret_i + 1


            if self.falsenode is not None:
                self.falsenode = ret_children_list[ret_i]

        return [ret_MCSsig_cnt, ret_mcs_breakpt, ret_terminal_node]


    def MCSBindGen_B(self, MCSsig_cnt, designbinddict_list, MCScommonbinddict, MCSbinddict_list, designtermdict_list, MCScommontermdict, MCSassign_analyzer, nextnode_str):

        #print("B redirected.....", end=' ')
        #self.toPrint()

        err = False
        if nextnode_str == 'condnode':
            print("B redirected.....condnode", end=' ')
            self.toPrint()

            [MCSsig_cnt, ret_mcs_breakpt_condnode, ret_terminal_node] = \
                self.condnode.MCSBindGen(None, MCSsig_cnt, designbinddict_list, MCScommonbinddict, MCSbinddict_list, designtermdict_list, MCScommontermdict, MCSassign_analyzer, True)

            self.condnode = ret_terminal_node
            if ret_mcs_breakpt_condnode == False: err = True


        elif nextnode_str == 'truenode':
            print("B redirected.....truenode", end=' ')
            self.toPrint()

            [MCSsig_cnt, ret_mcs_breakpt_truenode, ret_terminal_node] = \
                self.truenode.MCSBindGen(None, MCSsig_cnt, designbinddict_list, MCScommonbinddict, MCSbinddict_list, designtermdict_list, MCScommontermdict, MCSassign_analyzer, True)

            self.truenode = ret_terminal_node
            if ret_mcs_breakpt_truenode == False: err = True

        elif nextnode_str == 'falsenode':
            print("B redirected.....falsenode", end=' ')
            self.toPrint()

            [MCSsig_cnt, ret_mcs_breakpt_falsenode, ret_terminal_node] = \
                self.falsenode.MCSBindGen(None, MCSsig_cnt, designbinddict_list, MCScommonbinddict, MCSbinddict_list, designtermdict_list, MCScommontermdict, MCSassign_analyzer, True)

            self.falsenode = ret_terminal_node
            if ret_mcs_breakpt_falsenode == False: err = True


        if err:
            sys.stderr.write(type(self), ": Children are the same, and the structure is difference compared to previous designs, exit!")
            exit()

    def MCSBindGenSplitHead(self, new_node, old_node):

        if self.condnode is not None and id(self.condnode) == id(old_node):
            self.condnode = new_node

        elif self.truenode is not None and id(self.truenode) == id(old_node):
            self.truenode = new_node

        elif self.falsenode is not None and id(self.falsenode) == id(old_node):
            self.falsenode = new_node

    def fixpartsel(self, headScope, fixpartsel_termdict, fixpartsel_binddict, assign_analyzer, partsel_cnt_packaslist):

        maxbit = 0
        if self.condnode is not None:
            self.condnode.fixpartsel(headScope, fixpartsel_termdict, fixpartsel_binddict, assign_analyzer, partsel_cnt_packaslist)

        if self.truenode is not None:
            maxbit = self.truenode.fixpartsel(headScope, fixpartsel_termdict, fixpartsel_binddict, assign_analyzer, partsel_cnt_packaslist)

        if self.falsenode is not None:
            bit = self.falsenode.fixpartsel(headScope, fixpartsel_termdict, fixpartsel_binddict, assign_analyzer, partsel_cnt_packaslist)
            if maxbit < bit: maxbit = bit

        return maxbit

    def traverse(self, preNode, sigDiff, muxIdfy, options, info_dict, info_op = None, info_str=None):
        self.preNode = preNode


        ret =  str(self.matchedcnt)+'(Branch'
        if self.condnode is not None:

            #if not 'branch' in info_dict:
                #info_dict['branch'] = {}


            brIdfy = BrIdfy()
            # mark down the head node for that particular branch
            brIdfy.brInTree = self.condnode
            # use the node as key, and create MuxIdfy object to record multi-bit node number
            #brIdfy.muxIdfyEachBr = MuxIdfy(str(self.condnode))#TODO: The name might need to be fixed

            muxIdfy.brIdfyDict[self.condnode] = brIdfy

            ret += ' Cond:' + self.condnode.traverse(self.condnode, sigDiff, muxIdfy, options, info_dict, None, 'branch')
            # cmp operator shouldn't be able to go through branch, I think
        if self.truenode is not None: ret += ' True:' + self.truenode.traverse(preNode, sigDiff, muxIdfy, options, info_dict)
        if self.falsenode is not None: ret += ' False:'+ self.falsenode.traverse(preNode, sigDiff, muxIdfy, options, info_dict)
        ret += ')'
        return ret

    def muxModify(self, newScopeName_list, dinbool=None, din_repeatedstr=None):
        if self.condnode is not None: self.condnode.muxModify(newScopeName_list)
        if self.truenode is not None: self.truenode.muxModify(newScopeName_list)
        if self.falsenode is not None: self.falsenode.muxModify(newScopeName_list)


    def bindDestVModify(self, casenum, options, designnum, concatanalyzer, partselectanalyzer, sigdiffStr_Refmax, sigdiffStr_Maxbit, preNode = None, info_op = None):
        if self.truenode is not None:
            self.truenode.bindDestVModify(casenum, options, designnum, concatanalyzer, partselectanalyzer, sigdiffStr_Refmax, sigdiffStr_Maxbit, self, info_op)
        if self.falsenode is not None:
            self.falsenode.bindDestVModify(casenum, options, designnum, concatanalyzer, partselectanalyzer, sigdiffStr_Refmax, sigdiffStr_Maxbit, self, info_op)


    def rmvOldConnectNewNode(self, originalterminal, newtree):
        if self.truenode == originalterminal: self.truenode = newtree
        if self.falsenode == originalterminal: self.falsenode = newtree

    def bindDestBrModify(self, options, bindBrIdfyDict, designnum, partselectanalyzer, sigdiffStr_Refmax, sigdiffStr_Maxbit, isCond, preNode = None, info_op = None):
        if self.condnode is not None:
            self.condnode.bindDestBrModify(options, bindBrIdfyDict, designnum, partselectanalyzer, sigdiffStr_Refmax, sigdiffStr_Maxbit, True, self, info_op)
        if self.truenode is not None:
            self.truenode.bindDestBrModify(options, bindBrIdfyDict, designnum, partselectanalyzer, sigdiffStr_Refmax, sigdiffStr_Maxbit, isCond, self, info_op)
        if self.falsenode is not None:
            self.falsenode.bindDestBrModify(options, bindBrIdfyDict, designnum, partselectanalyzer, sigdiffStr_Refmax, sigdiffStr_Maxbit, isCond, self, info_op)


################################################################################
class DFEvalValue(DFNode):
    #for partsel on the lhs
    attr_names = ('value', 'width',)
    def __init__(self, value, width=32, isfloat=False, isstring=False):
        self.value = value
        self.width = width
        self.isfloat = isfloat
        self.isstring = isstring

        self.neighbour = []
    def __repr__(self):
        if self.isstring:
            return self.value
        ret = ''
        if self.value < 0: ret += '(-'
        if self.width != 32: ret += str(self.width)
        ret += "'d"
        ret += str(abs(self.value))
        if self.value < 0: ret += ')'
        return ret
    def tostr(self):
        if self.isstring:
            return self.value
        ret = ''
        if self.value < 0: ret += '(-'
        if self.width != 32: ret += str(self.width)
        ret += "'d"
        ret += str(abs(self.value))
        if self.value < 0: ret += ')'
        return ret
    def tocode(self, dest='dest'):
        return self.__repr__()

    def toPrint(self):
        print(str(self.selfdesignnum), id(self), self.parentstr, "DFEvalValue", str(self.value))

    def children(self):
        nodelist = []
        return tuple(nodelist)
    def eval(self):
        return self.value
    def __eq__(self, other):
        if type(self) != type(other): return False
        return self.value == other.value and self.width == other.width and self.isfloat == other.isfloat and self.isstring == other.isstring
    def __hash__(self):
        return hash((self.value, self.width, self.isfloat, self.isstring))

    def IDNeighbour(self,  preNode, headScope, design_i, designtermdict_list, preNode_level=None, info_str=None):
        self.selfdesignnum = design_i
        self.node_level = preNode_level + 1

        self.neighbour.append(preNode)
        self.parent = preNode
        self.parentstr = info_str
        self.selfstr = 'DFEvalValue'

        self.designAtoB_dict ={}
        self.designBtoA_dict = {}
        self.matchedcnt = 0

        self.headScope = headScope
        self.MCSbindgen_nodesplit = False
        self.MCSbindgen_visited = False

        self.term_width = int(self.width)

        return self.term_width

    def MCS_NodeCmp(self, DFNode_i):
        if type(self) == type(DFNode_i) and self.parentstr == DFNode_i.parentstr:
            return True
        else:
            return False

    def MCSBindGen(self, headnode, MCSsig_cnt, designbinddict_list, MCScommonbinddict, MCSbinddict_list, designtermdict_list, MCScommontermdict, MCSassign_analyzer, M_B_bool=None):
        return self.MCSBindGenDFNode( headnode, MCSsig_cnt, designbinddict_list, MCScommonbinddict, MCSbinddict_list, \
                                                                                   designtermdict_list, MCScommontermdict, MCSassign_analyzer, M_B_bool)


    def traverse(self, preNode, sigDiff, muxIdfy, options, info_dict, info_op = None, info_str=None):
        self.preNode = preNode

        return self.tostr()

class DFUndefined(DFNode):
    attr_names = ('width',)
    def __init__(self, width):
        self.width = width
        self.neighbour = []
    def __repr__(self):
        ret = ''
        if self.width != 32: ret += str(self.width)
        ret += "'d"
        ret += 'x'
        return ret
    def tostr(self):
        ret = ''
        if self.width != 32: ret += str(self.width)
        ret += "'d"
        ret += 'x'
        return ret
    def children(self):
        nodelist = []
        return tuple(nodelist)
    def __eq__(self, other):
        if type(self) != type(other): return False
        return self.width == other.width
    def __hash__(self):
        return hash(self.width)

    def toPrint(self):
        print(str(self.selfdesignnum), id(self), self.parentstr, "DFUndefined", str(self.width))

    def IDNeighbour(self,  preNode, headScope, design_i, designtermdict_list, preNode_level=None, info_str=None):
        self.selfdesignnum = design_i
        self.node_level = preNode_level + 1

        self.neighbour.append(preNode)
        self.parent = preNode
        self.parentstr = info_str
        self.selfstr = 'DFUndefined'

        self.designAtoB_dict ={}
        self.designBtoA_dict = {}
        self.matchedcnt = 0

        self.headScope = headScope
        self.MCSbindgen_nodesplit = False
        self.MCSbindgen_visited = False

        self.term_width = int(self.width)

        return self.term_width

    def MCS_NodeCmp(self, DFNode_i):
        if type(self) == type(DFNode_i) and self.parentstr == DFNode_i.parentstr:
            return True
        else:
            return False

    def MCSBindGen(self, headnode, MCSsig_cnt, designbinddict_list, MCScommonbinddict, MCSbinddict_list, designtermdict_list, MCScommontermdict, MCSassign_analyzer, M_B_bool=None):
        return self.MCSBindGenDFNode( headnode, MCSsig_cnt, designbinddict_list, MCScommonbinddict, MCSbinddict_list, \
                                                                                   designtermdict_list, MCScommontermdict, MCSassign_analyzer, M_B_bool)


    def traverse(self, preNode, sigDiff, muxIdfy, options, info_dict, info_op = None, info_str=None):
        self.preNode = preNode

        return self.tostr()

class DFHighImpedance(DFNode):
    attr_names = ('width',)
    def __init__(self, width):
        self.width = width
        self.neighbour = []
    def __repr__(self):
        ret = ''
        if self.width != 32: ret += str(self.width)
        ret += "'d"
        ret += 'z'
        return ret
    def tostr(self):
        ret = ''
        if self.width != 32: ret += str(self.width)
        ret += "'d"
        ret += 'z'
        return ret
    def children(self):
        nodelist = []
        return tuple(nodelist)
    def __eq__(self, other):
        if type(self) != type(other): return False
        return self.width == other.width
    def __hash__(self):
        return hash(self.width)

    def toPrint(self):
        print(str(self.selfdesignnum), id(self), self.parentstr, "DFHighImpedance", str(self.width))

    def IDNeighbour(self,  preNode, headScope, design_i, designtermdict_list, preNode_level=None, info_str=None):
        self.selfdesignnum = design_i
        self.node_level = preNode_level + 1

        self.neighbour.append(preNode)
        self.parent = preNode
        self.parentstr = info_str
        self.selfstr = 'DFHighImpedance'

        self.designAtoB_dict ={}
        self.designBtoA_dict = {}
        self.matchedcnt = 0

        self.headScope = headScope
        self.MCSbindgen_nodesplit = False
        self.MCSbindgen_visited = False

        self.term_width = int(self.width)

        return self.term_width

    def MCS_NodeCmp(self, DFNode_i):
        if type(self) == type(DFNode_i) and self.parentstr == DFNode_i.parentstr:
            return True
        else:
            return False

    def MCSBindGen(self, headnode, MCSsig_cnt, designbinddict_list, MCScommonbinddict, MCSbinddict_list, designtermdict_list, MCScommontermdict, MCSassign_analyzer, M_B_bool=None):
        return self.MCSBindGenDFNode( headnode, MCSsig_cnt, designbinddict_list, MCScommonbinddict, MCSbinddict_list, \
                                                                                    designtermdict_list, MCScommontermdict, MCSassign_analyzer, M_B_bool)


    def traverse(self, preNode, sigDiff, muxIdfy, options, info_dict, info_op = None, info_str=None):
        self.preNode = preNode

        return self.tostr()

################################################################################
class DFDelay(DFNotTerminal):
    attr_names = ()
    def __init__(self, nextnode):
        self.nextnode = nextnode
        self.neighbour = []
    def __repr__(self):
        return 'Delay'
    def tostr(self):
        ret = '(Delay '
        if self.nextnode is not None: ret += self.nextnode.tostr()
        ret += ')'
        return ret

    def tocode(self, dest='dest'):
        raise verror.DefinitionError('DFDelay does not support tocode()')
    def children(self):
        nodelist = []
        if self.nextnode is not None: nodelist.append(self.nextnode)
        return tuple(nodelist)
    def __eq__(self, other):
        if type(self) != type(other): return False
        return self.nextnodes == other.nextnodes
    def __hash__(self):
        return hash(tuple(self.nextnodes))

    def toPrint(self):
        print(str(self.selfdesignnum), id(self), self.parentstr, "DFDelay", self.nextnode)

    def IDNeighbour(self,  preNode, headScope, design_i, designtermdict_list, preNode_level=None, info_str=None):
        self.selfdesignnum = design_i
        self.node_level = preNode_level + 1

        self.term_width = 0

        self.neighbour.append(preNode)
        if self.nextnode is not None:
            self.neighbour.append(self.nextnode)
            self.term_width = self.nextnode.IDNeighbour(self, headScope, design_i, designtermdict_list, self.node_level + 1, "DFDelay")

        self.parent = preNode
        self.parentstr = info_str
        self.selfstr = 'DFDelay'

        self.designAtoB_dict ={}
        self.designBtoA_dict = {}
        self.matchedcnt = 0

        self.headScope = headScope
        self.MCSbindgen_nodesplit = False
        self.MCSbindgen_visited = False

        return self.term_width

    def IDFirstM_AB(self, designB_i, termo_set, designMCSOutput_list, designM_AB_initial_list, designF_A_list):

        if self.nextnode is not None:
            self.nextnode.IDFirstM_AB(designB_i, termo_set, designMCSOutput_list, designM_AB_initial_list, designF_A_list)

    def MCS_NodeCmp(self, DFNode_i):
        if type(self) == type(DFNode_i) and self.parentstr == DFNode_i.parentstr and type(self.nextnode) == type(DFNode_i.nextnode):
            return True
        else:
            return False

    def findGraphSize(self, designnum, mcshead_list, current_head, prenode_matcheddesign_i_list, mcsnode_cnt, mcsmatch_cnt):

        [self_case, self_head, self_matcheddesign_i_list, self_mcsnode_count, self_mcmatch_count] = \
            super(DFDelay, self).findGraphSize(designnum, mcshead_list, current_head, prenode_matcheddesign_i_list,
                                                  mcsnode_cnt, mcsmatch_cnt)

        ### using another var to avoid polluting self variable
        arg_head = self_head
        arg_node_cnt = self_mcsnode_count
        arg_match_cnt = self_mcmatch_count

        if self_case == MCS_NODE_UNMATCHED:
            arg_matcheddesign_i_list = []

        elif self_case == MCS_NODE_HEAD or self_case == MCS_NODE_SAME:
            arg_matcheddesign_i_list = copy.copy(self_matcheddesign_i_list)

        ### OKAY now go deeper
        if self.nextnode is not None:
            [arg_matcheddesign_i_list, arg_node_cnt, arg_match_cnt] = \
                self.findGraphSizeGoDeep(self.nextnode, designnum, mcshead_list, arg_head, arg_matcheddesign_i_list, arg_node_cnt, arg_match_cnt)

        # return var
        if self_case == MCS_NODE_UNMATCHED or self_case == MCS_NODE_HEAD:
            return [self_case, None, None, mcsnode_cnt, mcsmatch_cnt]

        else:  # the match list need to be updated by children
            return [self_case, current_head, arg_matcheddesign_i_list, arg_node_cnt, arg_match_cnt]

    def MCSBindGen(self, headnode, MCSsig_cnt, designbinddict_list, MCScommonbinddict, MCSbinddict_list, designtermdict_list, MCScommontermdict, MCSassign_analyzer, M_B_bool=None):
        children_list = [self.nextnode]
        childrenstr_list = []

        [ret_MCSsig_cnt, ret_mcs_breakpt, ret_terminal_node, ret_children_list] = self.MCSBindGenDFNotTerminal \
            (headnode, MCSsig_cnt, designbinddict_list, MCScommonbinddict, MCSbinddict_list, designtermdict_list, MCScommontermdict, MCSassign_analyzer, children_list, childrenstr_list, False, M_B_bool)

        return [ret_MCSsig_cnt, ret_mcs_breakpt, ret_terminal_node]

    def MCSBindGenSplitHead(self, new_node, old_node):

        if self.nextnode is not None:
            self.nextnode = new_node

    def fixpartsel(self, headScope, fixpartsel_termdict, fixpartsel_binddict, assign_analyzer, partsel_cnt_packaslist):
        if self.nextnode is not None:
            return self.nextnode.fixpartsel(headScope, fixpartsel_termdict, fixpartsel_binddict, assign_analyzer, partsel_cnt_packaslist)
        else:
            return 0

    def traverse(self, preNode, sigDiff, muxIdfy, options, info_dict, info_op = None, info_str=None):
        self.preNode = preNode

        ret = '(Delay '
        if self.nextnode is not None: ret += self.nextnode.traverse(preNode, sigDiff, muxIdfy, options, info_dict, info_op, info_str)
        ret += ')'

    def muxModify(self, newScopeName_list, dinbool=None, din_repeatedstr=None):
        if self.nextnode is not None: self.nextnode.muxModify(newScopeName_list)

    def bindDestVModify(self, casenum, options, designnum, concatanalyzer, partselectanalyzer, sigdiffStr_Refmax, sigdiffStr_Maxbit, preNode = None, info_op = None):
        if self.nextnode is not None:
            self.nextnode.bindDestVModify(casenum, options, designnum, concatanalyzer, partselectanalyzer, sigdiffStr_Refmax, sigdiffStr_Maxbit, self, info_op)

    def rmvOldConnectNewNode(self, originalterminal, newtree):
        if self.nextnode == originalterminal: self.nextnode = newtree

    def bindDestBrModify(self, options, bindBrIdfyDict, designnum, partselectanalyzer, sigdiffStr_Refmax, sigdiffStr_Maxbit, isCond, preNode = None, info_op = None):
        if self.nextnode is not None:
            self.bindDestBrModify(options, bindBrIdfyDict, designnum, partselectanalyzer, sigdiffStr_Refmax, sigdiffStr_Maxbit, isCond, self, info_op)

################################################################################
class DFSyscall(DFNotTerminal):
    attr_names = ()
    def __init__(self, syscall, nextnodes):
        self.syscall = syscall
        self.nextnodes = nextnodes
        self.neighbour = []
    def __repr__(self):
        return 'Syscall'
    def tostr(self):
        ret = '(Syscall '
        ret += self.syscall
        ret += ' Next:'
        for n in self.nextnodes: ret += n.tostr() + ','
        ret = ret[0:-1] + ')'
        return ret

    def tocode(self, dest='dest'):
        ret = '$' + self.syscall + '('
        for n in self.nextnodes: ret += n.tocode(dest) + ','
        ret = ret[:-1]
        ret += ')'
        return ret
    def children(self):
        nodelist = []
        if self.nextnodes is not None: nodelist.extend(self.nextnodes)
        return tuple(nodelist)
    def __eq__(self, other):
        if type(self) != type(other): return False
        if self.syscall != other.syscall: return False
        return self.nextnodes == other.nextnodes
    def __hash__(self):
        return hash(tuple(self.nextnodes))

    def toPrint(self):
        print(str(self.selfdesignnum), id(self), self.parentstr, "DFSyscall", self.nextnodes)

    def IDNeighbour(self,  preNode, headScope, design_i, designtermdict_list, preNode_level=None, info_str=None):
        self.selfdesignnum = design_i
        self.node_level = preNode_level + 1

        self.neighbour.append(preNode)
        for i, n in enumerate(self.nextnodes):
            self.neighbour.append(n)
            n.IDNeighbour(self, headScope, design_i, designtermdict_list, self.node_level + 1, "DFSyscall_" + str(i))
        self.parent = preNode
        self.parentstr = info_str
        self.selfstr = self.syscall

        self.designAtoB_dict ={}
        self.designBtoA_dict = {}
        self.matchedcnt = 0

        self.headScope = headScope
        self.MCSbindgen_nodesplit = False
        self.MCSbindgen_visited = False

        self.term_width = 0
        return self.term_width

    def IDFirstM_AB(self, designB_i, termo_set, designMCSOutput_list, designM_AB_initial_list, designF_A_list):

        for n in self.nextnodes:
            n.IDFirstM_AB(designB_i, termo_set, designMCSOutput_list, designM_AB_initial_list, designF_A_list)

    def MCS_NodeCmp(self, DFNode_i):
        if type(self) == type(DFNode_i) and self.syscall == DFNode_i.syscall and self.parentstr == DFNode_i.parentstr:
            return True
        else:
            return False

    def findGraphSize(self, designnum, mcshead_list, current_head, prenode_matcheddesign_i_list, mcsnode_cnt, mcsmatch_cnt):

        [self_case, self_head, self_matcheddesign_i_list, self_mcsnode_count, self_mcmatch_count] = \
            super(DFSyscall, self).findGraphSize(designnum, mcshead_list, current_head, prenode_matcheddesign_i_list,
                                                  mcsnode_cnt, mcsmatch_cnt)

        ### using another var to avoid polluting self variable
        arg_head = self_head
        arg_node_cnt = self_mcsnode_count
        arg_match_cnt = self_mcmatch_count

        if self_case == MCS_NODE_UNMATCHED:
            arg_matcheddesign_i_list = []

        elif self_case == MCS_NODE_HEAD or self_case == MCS_NODE_SAME:
            arg_matcheddesign_i_list = copy.copy(self_matcheddesign_i_list)

        ### OKAY now go deeper
        for n in self.nextnodes:
            [arg_matcheddesign_i_list, arg_node_cnt, arg_match_cnt] = \
                self.findGraphSizeGoDeep(n, designnum, mcshead_list, arg_head, arg_matcheddesign_i_list, arg_node_cnt, arg_match_cnt)

        # return var
        if self_case == MCS_NODE_UNMATCHED or self_case == MCS_NODE_HEAD:
            return [self_case, None, None, mcsnode_cnt, mcsmatch_cnt]

        else:  # the match list need to be updated by children
            return [self_case, current_head, arg_matcheddesign_i_list, arg_node_cnt, arg_match_cnt]


    def fixpartsel(self, headScope, fixpartsel_termdict, fixpartsel_binddict, assign_analyzer, partsel_cnt_packaslist):
        max_bit = 0
        for n in self.nextnodes:
            bit = n.fixpartsel(headScope, fixpartsel_termdict, fixpartsel_binddict, assign_analyzer, partsel_cnt_packaslist)
            if max_bit < bit: max_bit = bit
        return max_bit

    def traverse(self, preNode, sigDiff, muxIdfy, options, info_dict, info_op = None, info_str=None):
        self.preNode = preNode

        ret = '(Syscall '
        ret += self.syscall
        ret += ' Next:'
        for n in self.nextnodes: ret += n.traverse(preNode, sigDiff, muxIdfy, options, info_dict, info_op, info_str) + ','
        ret = ret[0:-1] + ')'
        return ret

    def muxModify(self, newScopeName_list, dinbool=None, din_repeatedstr=None):
        for n in self.nextnodes: n.muxModify(newScopeName_list)

    def bindDestVModify(self, casenum, options, designnum, concatanalyzer, partselectanalyzer, sigdiffStr_Refmax, sigdiffStr_Maxbit, preNode = None, info_op = None):
        for n in self.nextnodes:
            n.bindDestVModify(casenum, options, designnum, concatanalyzer, partselectanalyzer, sigdiffStr_Refmax, sigdiffStr_Maxbit, self, info_op)

    def rmvOldConnectNewNode(self, originalterminal, newtree):
        for i, n in enumerate(self.nextnodes):
            if n == originalterminal:
                self.nextnodes = self.nextnodes[:i] + (newtree,) + self.nextnodes[:i + 1]
                break

    def bindDestBrModify(self, options, bindBrIdfyDict, designnum, partselectanalyzer, sigdiffStr_Refmax, sigdiffStr_Maxbit, isCond, preNode = None, info_op = None):
        for n in self.nextnodes:
            n.bindDestBrModify(options, bindBrIdfyDict, designnum, partselectanalyzer, sigdiffStr_Refmax, sigdiffStr_Maxbit, isCond, self, info_op)


################################################################################
class Term(object):
    def __init__(self,name,termtype=(),msb=None,lsb=None,lenmsb=None,lenlsb=None):
        self.name = name # tuple (str)
        self.termtype = termtype # set (str)
        self.msb = msb # DFNode
        self.lsb = lsb # DFNode
        self.lenmsb = lenmsb # DFNode
        self.lenlsb = lenlsb # DFNode
        self.bitwidth = 0
    def __repr__(self):
        return str(self.name)
    def tostr(self):
        ret = '(Term name:' + str(self.name) + ' type:' + str(sorted(self.termtype, key=lambda x:str(x)))
        if self.msb is not None: ret += ' msb:' + self.msb.tostr()
        if self.lsb is not None: ret += ' lsb:' + self.lsb.tostr()
        if self.lenmsb is not None: ret += ' lenmsb:' + self.lenmsb.tostr()
        if self.lenlsb is not None: ret += ' lenlsb:' + self.lenlsb.tostr()
        ret += ')'
        return ret
    def __ne__(self, other):
        return not self.__eq__(other)
    def __eq__(self, other):
        if type(self) != type(other): return False
        return self.name == other.name and self.termtype == other.termtype and self.msb == other.msb and self.lsb == other.lsb and self.lenmsb == other.lenmsb and self.lenlsb == other.lenlsb
    def __hash__(self):
        return hash((self.name, self.termtype, self.msb, self.lsb, self.lenmsb, self.lenlsb))

    ############################################################################
    def getScope(self, termname):
        return termname[:-1]

    def isTopmodule(self, scope):
        if len(scope)==1: return True
        return False

    ############################################################################
    def tocode(self):
        flatname = util.toFlatname(self.name)
        scope = self.getScope(self.name)
        code = ''
        if self.isTopmodule(scope):
            if signaltype.isInput(self.termtype): code += 'input '
            elif signaltype.isInout(self.termtype): code += 'inout '
            elif signaltype.isOutput(self.termtype): code += 'output '
        else:
            if signaltype.isInput(self.termtype): code += 'wire '
            elif signaltype.isInout(self.termtype): code += 'wire '
            elif signaltype.isOutput(self.termtype) and not signaltype.isReg(self.termtype): code += 'wire '

        if signaltype.isReg(self.termtype): code += 'reg '
        if signaltype.isRegArray(self.termtype): code += 'reg '
        if signaltype.isWire(self.termtype): code += 'wire '
        if signaltype.isWireArray(self.termtype): code += 'wire '
        if signaltype.isInteger(self.termtype): code += 'integer '
        if signaltype.isFunction(self.termtype): code += 'wire '
        if signaltype.isRename(self.termtype): code += 'wire '

        if (not signaltype.isInteger(self.termtype) and
            self.msb is not None and self.lsb is not None):
            code += '[' + self.msb.tocode(None) + ':' + self.lsb.tocode(None) + '] '
        code += flatname # signal name
        if self.lenmsb is not None and self.lenlsb is not None:
            code += ' [' + self.lenmsb.tocode() + ':' + self.lenlsb.tocode(flatname) + ']'
        code += ';\n'
        return code

    def muxModify(self, newScopeName_list, dinbool=None, din_repeatedstr=None):
        if self.msb is not None: self.msb.muxModify(newScopeName_list, dinbool, din_repeatedstr)
        if self.lsb is not None: self.lsb.muxModify(newScopeName_list, dinbool, din_repeatedstr)
        if self.lenmsb is not None: self.lenmsb.muxModify(newScopeName_list, dinbool, din_repeatedstr)
        if self.lenlsb is not None: self.lenlsb.muxModify(newScopeName_list, dinbool, din_repeatedstr)




################################################################################
class Bind(object):

    def __init__(self, tree, dest, msb=None, lsb=None, ptr=None, alwaysinfo=None, parameterinfo=''):
        self.tree = tree
        self.dest = dest
        self.msb = msb
        self.lsb = lsb
        self.ptr = ptr
        self.alwaysinfo = alwaysinfo
        self.parameterinfo = parameterinfo

        self.neighbour = []

        if dest is None: raise verror.DefinitionError('Bind dest is empty')

    def __ne__(self, other):
        return not self.__eq__(other)
    def __eq__(self, other):
        if type(self) != type(other): return False
        return self.tree == other.tree and self.dest == other.dest and self.msb == other.msb and self.lsb == other.lsb and self.ptr == other.ptr and self.alwaysinfo == other.alwaysinfo and self.parameterinfo == other.parameterinfo
    def __hash__(self):
        return hash((self.tree, self.dest, self.msb, self.lsb, self.ptr, self.alwaysinfo, self.parameterinfo))

    def isCombination(self):
        if self.alwaysinfo is None: return True
        if self.alwaysinfo.isCombination(): return True
        return False

    def tostr(self):
        ret = '(Bind'
        if self.dest is not None: ret += ' dest:' + str(self.dest)
        if self.msb is not None: ret += ' msb:' + self.msb.tostr()
        if self.lsb is not None: ret += ' lsb:' + self.lsb.tostr()
        if self.ptr is not None: ret += ' ptr:' + self.ptr.tostr()
        if self.tree is not None: ret += ' tree:' + self.tree.tostr()
        ret += ')'
        return ret

    def tocode(self):
        if self.parameterinfo == 'parameter': return self._parameter()
        if self.parameterinfo == 'localparam': return self._localparam()
        if self.alwaysinfo is None: return self._assign()
        if self.alwaysinfo.isCombination(): return self._always_combination()
        else: return self._always_clockedge()

    def getdest(self):
        dest = util.toFlatname(self.dest)
        if self.ptr is not None:
            dest += '[' + self.ptr.tocode(None) + ']'
        if self.msb is not None and self.lsb is not None:
            msbcode = self.msb.tocode(None)
            lsbcode = self.lsb.tocode(None)
            if msbcode == lsbcode:
                dest += '[' + msbcode + ']'
            else:
                dest += '[' + msbcode + ':' + lsbcode + ']'
        return dest

    def _parameter(self):
        dest = self.getdest()
        code = 'parameter ' + dest
        code += ' = ' + self.tree.tocode(dest) + ';\n'
        return code

    def _localparam(self):
        dest = self.getdest()
        code = 'localparam ' + dest
        code += ' = ' + self.tree.tocode(dest) + ';\n'
        return code

    def _assign(self):
        dest = self.getdest()
        code = 'assign ' + dest
        code += ' = ' + self.tree.tocode(dest) + ';\n'
        return code

    def _always_clockedge(self):
        dest = self.getdest()
        code = 'always @('
        if self.alwaysinfo.clock_edge is not None and self.alwaysinfo.clock_name is not None:
            code += self.alwaysinfo.clock_edge + ' '
            code += util.toFlatname(self.alwaysinfo.clock_name)
        if self.alwaysinfo.reset_edge is not None and self.alwaysinfo.reset_name is not None:
            code += ' or '
            code += self.alwaysinfo.reset_edge + ' '
            code += util.toFlatname(self.alwaysinfo.reset_name)
        code += ') begin\n'
        if isinstance(self.tree, DFBranch):
            code += self.tree.tocode(dest, always='clockedge')
        else:
            code += dest
            code += ' <= ' + self.tree.tocode(dest) + ';\n'
        code += 'end\n'
        code += '\n'
        return code

    def _always_combination(self):
        dest = self.getdest()
        code = ''
        code += 'always @*'
        code += ' begin\n'
        if isinstance(self.tree, DFBranch):
            code += self.tree.tocode(dest, always='combination')
        else:
            code += dest
            code += ' = ' + self.tree.tocode(dest) + ';\n'
        code += 'end\n'
        code += '\n'
        return code

    def isClockEdge(self):
        if self.alwaysinfo is None: return False
        return self.alwaysinfo.isClockEdge()
    def getClockName(self):
        if self.alwaysinfo is None: return ''
        return self.alwaysinfo.getClockName()
    def getClockEdge(self):
        if self.alwaysinfo is None: return ''
        return self.alwaysinfo.getClockEdge()
    def getClockBit(self):
        if self.alwaysinfo is None: return ''
        return self.alwaysinfo.getClockBit()
    def getResetName(self):
        if self.alwaysinfo is None: return ''
        return self.alwaysinfo.getResetName()
    def getResetEdge(self):
        if self.alwaysinfo is None: return ''
        return self.alwaysinfo.getResetEdge()
    def getResetBit(self):
        if self.alwaysinfo is None: return ''
        return self.alwaysinfo.getResetBit()
    def getSenslist(self):
        if self.alwaysinfo is None: return ''
        return self.alwaysinfo.getSenslist()

    def toPrint(self):
        print(str(self.selfdesignnum), "Bind", id(self), str(self.dest))

    def toStrForBveTest(self):
        ret = ''
        if self.dest is not None: ret += ' dest:' + str(self.dest)
        if self.msb is not None: ret += ' msb:' + self.msb.tostr()
        if self.lsb is not None: ret += ' lsb:' + self.lsb.tostr()

        return ret

    def IDNeighbour(self,  preNode, headScope, design_i, designtermdict_list, bvhasmulti, preNode_level=None, info_str=None):
        self.selfdesignnum = design_i
        self.node_level = 0

        #if self.dest is not None:
            #self.neighbour.append(self.dest)
            #self.dest.IDNeighbour(self)

        # if self.msb is not None:
        #     self.neighbour.append(self.msb)
        #     self.msb.IDNeighbour(self)
        #
        # if self.lsb is not None:
        #     self.neighbour.append(self.lsb)
        #     self.lsb.IDNeighbour(self)

        if self.ptr is not None:
            self.neighbour.append(self.ptr)
            self.ptr.IDNeighbour(self, headScope, design_i, designtermdict_list, self.node_level + 1, "Bind_ptr")

        if self.tree is not None:
            self.neighbour.append(self.tree)
            self.tree.IDNeighbour(self, headScope, design_i, designtermdict_list, self.node_level + 1,  "Bind_tree")

        self.parent = self.dest
        self.parentstr = info_str
        self.selfstr = str(self.dest)

        self.designAtoB_dict ={}
        self.designBtoA_dict = {}
        self.matchedcnt = 0

        self.headScope = headScope
        self.MCSbindgen_nodesplit = False
        self.MCSbindgen_visited = False

        self.bvhasmulti = bvhasmulti

        if self.msb == None and self.lsb == None:
            term = designtermdict_list[self.selfdesignnum][self.dest]
            self.term_width = self.codeToValue(term.msb.tocode()) - self.codeToValue(term.lsb.tocode()) + 1
        else:
            self.term_width = self.msb.tocode() - self.lsb.tocode() + 1



    def IDFirstM_AB(self, designB_i, termo_set, designMCSOutput_list, designM_AB_initial_list, designF_A_list):

        if self.ptr is not None:
            self.ptr.IDFirstM_AB(designB_i, termo_set, designMCSOutput_list, designM_AB_initial_list, designF_A_list)

        if self.tree is not None:
            self.tree.IDFirstM_AB(designB_i, termo_set, designMCSOutput_list, designM_AB_initial_list, designF_A_list)


    def MCS_NodeCmp(self, DFNode_i):
        if type(self) == type(DFNode_i) and str(self.dest) == str(DFNode_i.dest):# and self.parentstr == DFNode.parentstr
            return True
        else:
            return False

    def findGraphSize(self, designnum):

        mcshead_list = []

        current_head = None
        self_matcheddesign_i_list = []
        mcsnode_cnt = 0
        mcsmatch_cnt = 0

        self.graphsize = 0
        self.matcheddesign = self_matcheddesign_i_list


        for designmatched_i in range(0, designnum):

            if self.bvhasmulti == False and designmatched_i in self.designAtoB_dict and designmatched_i != self.selfdesignnum:
                self_matcheddesign_i_list.append(True)
                mcsmatch_cnt = mcsmatch_cnt + 1
            else:
                self_matcheddesign_i_list.append(False)

        # Since it is the head, if there is a match, than node_cnt must be 1
        if self.bvhasmulti == False and self.designAtoB_dict:
            mcshead_list.append(self)
            mcsnode_cnt = 1


            current_head = self
            current_head.graphsize = mcsnode_cnt
            current_head.matchsize = mcsmatch_cnt

        if self.ptr is not None:
            self.ptr.findGraphSize(designnum, mcshead_list, current_head, self_matcheddesign_i_list, mcsnode_cnt, mcsmatch_cnt)

        if self.tree is not None:
            self.tree.findGraphSize(designnum, mcshead_list, current_head, self_matcheddesign_i_list, mcsnode_cnt, mcsmatch_cnt)

        return mcshead_list

    def MCSBindGen(self, headnode, MCSsig_cnt, designbinddict_list, MCScommonbinddict, MCSbinddict_list, designtermdict_list, MCScommontermdict, MCSassign_analyzer, M_B_bool=None):

        ### First Node should be with mcs <- actually that may not be true

        if self.MCSbindgen_visited == True:
            print("binddest already visited.....", end=' ')
            self.toPrint()
            # bcos it is replicated, so return false even if it is a breakpt
            return [MCSsig_cnt, False, None]

        # put self into global common bindlist, and remove that from each of the node
        MCScommonbinddict[self.dest] = designbinddict_list[self.selfdesignnum][self.dest]
        del designbinddict_list[self.selfdesignnum][self.dest]


        self.MCSbindgen_visited = True
        for di, dv in enumerate(headnode.matcheddesign):
            if dv == True:
                nodeB = self.designAtoB_dict[di]
                nodeB.MCSbindgen_visited = True

                del designbinddict_list[di][nodeB.dest]



        if self.ptr is not None:
            [ret_MCSsig_cnt, ret_mcs_breakpt, ret_terminal_node] = \
                self.ptr.MCSBindGen(headnode, MCSsig_cnt, designbinddict_list, MCScommonbinddict, MCSbinddict_list, designtermdict_list, MCScommontermdict, MCSassign_analyzer, M_B_bool)

            if ret_mcs_breakpt == True:
                self.ptr = ret_terminal_node

                for di, dv in enumerate(headnode.matcheddesign):
                    if dv == True:
                        self.designAtoB_dict[di].MCSBindGen_B(MCSsig_cnt, designbinddict_list, MCSbinddict_list, designtermdict_list, MCScommontermdict, MCSassign_analyzer, 'ptr')
            MCSsig_cnt = ret_MCSsig_cnt


        if self.tree is not None:
            [ret_MCSsig_cnt, ret_mcs_breakpt, ret_terminal_node] = \
                self.tree.MCSBindGen(headnode, MCSsig_cnt, designbinddict_list, MCScommonbinddict, MCSbinddict_list, designtermdict_list, MCScommontermdict, MCSassign_analyzer, M_B_bool)

            if ret_mcs_breakpt == True:
                self.tree = ret_terminal_node

                for di, dv in enumerate(headnode.matcheddesign):
                    if dv == True:
                        self.designAtoB_dict[di].MCSBindGen_B(MCSsig_cnt, designbinddict_list, MCScommonbinddict, MCSbinddict_list, designtermdict_list, MCScommontermdict, MCSassign_analyzer, 'tree')
            MCSsig_cnt = ret_MCSsig_cnt



        return [MCSsig_cnt, True, None]


    def MCSBindGen_B(self, MCSsig_cnt, designbinddict_list, MCScommonbinddict, MCSbinddict_list, designtermdict_list, MCScommontermdict, MCSassign_analyzer, nextnode_str):

        print("B redirected.....", end=' ')
        self.toPrint()

        err = False
        if nextnode_str == 'ptr':
            [MCSsig_cnt, ret_mcs_breakpt_ptr, ret_terminal_node] = \
                self.ptr.MCSBindGen(None, MCSsig_cnt, designbinddict_list, MCScommonbinddict, MCSbinddict_list, designtermdict_list, MCScommontermdict, MCSassign_analyzer, True)

            self.ptr = ret_terminal_node

            if ret_mcs_breakpt_ptr == False:
                err = True

        elif nextnode_str == 'tree':
            [MCSsig_cnt, ret_mcs_breakpt_tree, ret_terminal_node] = \
                self.tree.MCSBindGen(None, MCSsig_cnt, designbinddict_list, MCScommonbinddict, MCSbinddict_list, designtermdict_list, MCScommontermdict, MCSassign_analyzer, True)

            self.tree = ret_terminal_node

            if ret_mcs_breakpt_tree == False:
                err = True


        if err:
            sys.stderr.write(str(type(self)) +  ": Children are the same, and the structure is difference compared to previous designs, exit!\n")
            exit()

    def fixpartsel(self, headScope, fixpartsel_termdict, fixpartsel_binddict, assign_analyzer, partsel_cnt_packaslist):
        if self.ptr is not None: self.ptr.fixpartsel(headScope, fixpartsel_termdict, fixpartsel_binddict, assign_analyzer, partsel_cnt_packaslist)
        if self.tree is not None: self.tree.fixpartsel(headScope, fixpartsel_termdict, fixpartsel_binddict, assign_analyzer, partsel_cnt_packaslist)


    def MCSBindGenSplitHead(self, new_node, old_node):

        if self.ptr is not None and id(self.ptr) == id(old_node):
            self.ptr = new_node

        elif self.tree is not None and id(self.tree) == id(old_node):
            self.tree = new_node

    def traverse(self, sigDiff, muxIdfy, options, info_dict, info_op = None, info_str=None):

        ret =  str(self.matchedcnt)+'(Bind'
        if self.dest is not None:
            ret += ' dest:' + str(self.dest)

            if  str(self.dest) in sigDiff:
                self.mux = True
                muxIdfy.headmux = True

        if self.msb is not None: ret += ' msb:' + self.msb.traverse(self, sigDiff, muxIdfy, options, info_dict)
        if self.lsb is not None: ret += ' lsb:' + self.lsb.traverse(self, sigDiff, muxIdfy, options, info_dict)
        if self.ptr is not None: ret += ' ptr:' + self.ptr.traverse(self, sigDiff, muxIdfy, options, info_dict)
        if self.tree is not None: ret += ' tree:' + self.tree.traverse(self, sigDiff, muxIdfy, options, info_dict)
        ret += ')'
        return ret

    def muxModify(self, newScopeName_list, dinbool=None, din_repeatedstr=None):
        if self.tree is not None: self.tree.muxModify(newScopeName_list, dinbool, din_repeatedstr)


    def bindDestVModify(self, casenum, options, designnum, concatanalyzer, partselectanalyzer, sigdiffStr_Refmax, \
                                                            sigdiffStr_Maxbit, preNode = None, info_op = None):
        if self.tree is not None:
            self.tree.bindDestVModify(casenum, options, designnum, concatanalyzer, partselectanalyzer, sigdiffStr_Refmax, sigdiffStr_Maxbit, self, info_op)

    def concatBindDestVModify(self, originalterminal, maxbit, bitdiff, preNode):
        if self.tree is not None:
            self.tree.concatBindDestVModify(originalterminal, maxbit, bitdiff, preNode)

    def partselectBindDestVModify(self, originalterminal, maxbit, bitdiff, preNode):
        if self.tree is not None:
            self.tree.partselectBindDestVModify(originalterminal, maxbit, bitdiff, preNode)

    def rmvOldConnectNewNode(self, originalterminal, newtree):
        if self.tree == originalterminal:
            self.tree = newtree


    def bindDestBrModify(self, options, bindBrIdfyDict, designnum, partselectanalyzer, sigdiffStr_Refmax, sigdiffStr_Maxbit, isCond, preNode = None, info_op = None):
        if self.tree is not None:
            self.tree.bindDestBrModify(options, bindBrIdfyDict, designnum, partselectanalyzer, sigdiffStr_Refmax, sigdiffStr_Maxbit, isCond, self)

    def codeToValue(self, instr):
        str_list = re.split('(\+|\-|\*|\(|\))', instr)

        out_str = ''
        for s in str_list:
            if '\'b' in s:
                out_str += str(int(s[s.index('\'b') + 2:], 2))
            else:
                out_str += s
        if out_str.isdigit():
            return int(out_str)
        else:
            return eval(out_str)



################################################################################
class DataFlow(object):
    def __init__(self):
        self.terms = {}
        self.binddict = {}

        self.functions = {}
        self.function_ports = {}
        self.tasks = {}
        self.task_ports = {}
        self.temporal_value = {}

    ############################################################################
    def addTerm(self, name, term):
        if not name in self.terms:
            self.terms[name] = term
        else:
            self.setTerm(name, term)

    def setTerm(self, name, term):
        self.terms[name].termtype |= term.termtype
        if self.terms[name].msb is None: self.terms[name].msb = term.msb
        if self.terms[name].lsb is None: self.terms[name].lsb = term.lsb
        if self.terms[name].lenmsb is None: self.terms[name].lenmsb = term.lenmsb
        if self.terms[name].lenlsb is None: self.terms[name].lenlsb = term.lenlsb

    def hasTerm(self, name):
        return name in self.terms

    def getTerm(self, name):
        if name in self.terms: return self.terms[name]
        return None

    def getTerms(self):
        return self.terms

    ############################################################################
    def addBind(self, name, bind):
        if name is None:
            raise verror.DefinitionError('Bind name is empty')
        if not name in self.binddict:
            self.binddict[name] = [bind,]
        else:
            self.setBind(name, bind)

    def setBind(self, name, bind):
        if name is None:
            raise verror.DefinitionError('Bind name is empty')
        currentbindlist = self.binddict[name]
        c_i = 0
        for c in currentbindlist:
            if c.msb == bind.msb and c.lsb == bind.lsb and c.ptr == bind.ptr:
                self.binddict[name][c_i].tree = bind.tree
                return
            c_i += 1
        self.binddict[name] = currentbindlist + [bind,]

    def getBindlist(self, name):
        if name in self.binddict: return tuple(self.binddict[name])
        return ()

    def getBinddict(self):
        return self.binddict

    ############################################################################
    def addFunction(self, name, definition):
        self.functions[name] = definition
    def hasFunction(self, name):
        return name in self.functions
    def getFunction(self, name):
        if name in self.functions: return self.functions[name]
        return None
    def addFunctionPorts(self, name, ports):
        self.function_ports[name] = ports
    def getFunctionPorts(self, name):
        if name in self.function_ports: return self.function_ports[name]
        return ()

    ############################################################################
    def addTask(self, name, definition):
        self.tasks[name] = definition
    def hasTask(self, name):
        return name in self.tasks
    def getTask(self, name):
        if name in self.tasks: return self.tasks[name]
        return None
    def addTaskPorts(self, name, ports):
        self.task_ports[name] = ports
    def getTaskPorts(self, name):
        if name in self.task_ports: return self.task_ports[name]
        return ()

    ############################################################################
    def setTemporalValue(self, name, value):
        self.temporal_value[name] = value
    def getTemporalValue(self, name):
        return self.temporal_value[name]





class MuxIdfy(object):
    # 4 cases
    headmux = False
    constantNum = 0
    termNum = 0
    termMultiNum = 0

    hasCmp = False

    brIdfyDict = {}

    # set in 2nd parse
    #childSomedemux = False
    #childAlldemux = False

    nameStr = ""

    def __init__(self, nameStr):
        self.nameStr = nameStr

    def toStr(self):
        return self.nameStr + ": Headmuxed->" + str(self.headmux) + " termMultiNum->" + str(self.termMultiNum) + \
               " termNum->" + str(self.termNum)

class BrIdfy(object):

    brInTree = None

    constantNum = 0
    termNum = 0
    termMultiNum = 0
    hasCmp = False
    #muxIdfyEachBr = None
    lastSeenOp = None


class DesignBindDest(object):
    designNum = 0
    bindDestList = []
    processed = False

    def __init__(self, designNum, bindDestList):
        self.designNum = designNum
        self.bindDestList = bindDestList



class MCS_Node_Container(object):

    def __init__(self):
        self.d = {}


    def insertNode(self, e):
        if e not in self.d:
            self.d[e] = []
        self.d[e].append(e)

    def getNode(self, e):
        if e in self.d:
            for dv in self.d[e]:
                if id(dv) == id(e): return e
        return None

    def getNodesinList(self):
        retlist = []
        for di, dlist in self.d.items():
            for dv in dlist:
                retlist.append(dv)
        return retlist

    # this is designed to check the output node only
    def matchNode_Output(self, e, designnum):
        if e in self.d:
            for dv in self.d[e]:
                # return the 1st element only, coz everytime u will need one node
                if dv.output_matched != designnum and e.MCS_NodeCmp(dv):
                    return dv


    def rmvNode(self, e):
        if e in self.d:
            for i in xrange(len(self.d) - 1, -1, -1):
                if id(self.d[i]) == id(e): del self.d[i]

    def isEmpty(self):
        if not self.d:
            return True
        else:
            return False

    def getLength(self):
        if not self.d:
            return 0
        else:
            count = 0
            for di, dv in self.d.items():
                count = count + len(dv)
            return count


class MCS_M_AB(object):

    def __init__(self):
        self.dict_A_refB = {}
        self.dict_B = {}

    def insertNode_M_AtoB(self, e_A, e_B):

        if e_A not in self.dict_A_refB:
            self.dict_A_refB[e_A] = []
        self.dict_A_refB[e_A].append([e_A, e_B])

    def insertNode_M_B(self, e_B):

        if e_B not in self.dict_B:
            self.dict_B[e_B] = []
        self.dict_B[e_B].append(e_B)


    def getNode_M_A(self, e_A):
        if e_A in self.dict_A_refB:
            for e_Av in self.dict_A_refB[e_A]:
                if id(e_Av[0]) == id(e_A): return e_A
        return None

    def getNode_M_B(self, e_B):
        if e_B in self.dict_B:
            for e_Bv in self.dict_B[e_B]:
                if id(e_Bv) == id(e_B): return e_B
            return None


    def getNodes_M_A_List(self):
        retlist = []
        for di, dlist in self.dict_A_refB.items():
            for dv in dlist:
                retlist.append(dv[0])
        return retlist


    def getNodesM_B_List(self):
        retlist = []
        for di, dlist in self.dict_B.items():
            for dv in dlist:
                retlist.append(dv)
        return retlist

    def map_M_A_to_M_B(self, e_A):
        if e_A in self.dict_A_refB:
            for e_Av in self.dict_A_refB[e_A]:
                if id(e_Av[0]) == id(e_A): return e_Av[1]
        return None


class MCS_D_A():

    def __init__(self):
        self.d = {}
        self.ranking = []

    def isEmpty(self):
        if not self.ranking: return True
        else: return False

    def getNode(self, e):
        if e in self.d:
            for e_v in self.d[e]:
                if id(e_v) == id(e): return e_v
        return None

    # The format of ranking is as follows:
    # {e_key: [ [<element0>, [<element1>], .................], ......}
    def insertNode(self, e):
        if e not in self.d:
            self.d[e] = []
        self.d[e].append(e)

        self.ranking.insert(0, e)

    def chooseNode(self):
        if not self.ranking: return None
        else:
            chosen_e = self.ranking.pop(0)
            chosen_list = self.d[chosen_e]

            for i in range(len(chosen_list) - 1, -1, -1):
                if id(chosen_list[i]) == id(chosen_e):
                    del chosen_list[i]
                    break

            if len(chosen_list) == 0:
                del self.d[chosen_e]

            return chosen_e

    def lowerNode(self, e):
        #print("><><><><><><><><><><><><><> neighbour to lower", e.tostr())
        if not e in self.d:
           return
        else:
            #check if the node exists
            for lw_e in self.d[e]:
                if id(lw_e) == id(e):
                    # check in ranking and find out which position it is
                    for i in range(len(self.ranking) - 2, -1, -1):
                        if id(self.ranking[i]) == id(e):
                            self.ranking.pop(i)
                            self.ranking.append(e)
                            #print("><><><><><><><><><><><><><>><><><><><><><><><><><><><> moved neighbour", e, "\n")


