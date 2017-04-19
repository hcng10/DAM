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
    # preNode: refers to the head, or the starting point of the conditional in branch
    def traverse(self, preNode, sigDiff, muxIdfy, options, info_dict, info_op = None, info_str=None):pass
    # This function is only used in mux structure, and only the terminal needs to be changed :)
    def muxModify(self, newScopeName_list, dinbool=None, din_repeatedstr=None): pass

    # preNode: refers to the node right above >< sorry it is a bit confusing
    def bindDestVModify(self, options, casenum, designnum, concatanalyzer, partselectanalyzer, sigdiffStr_Refmax, sigdiffStr_Maxbit, preNode = None, info_op = None): pass
    def concatBindDestVModify(self, originalterminal, maxbit, bitdiff, preNode = None): pass
    def partselectBindDestVModify(self, originalterminal, maxbit, bitdiff, preNode = None): pass
    def rmvOldConnectNewNode(self, originalterminal, newtree): pass
    def bindDestBrModify(self, options, bindBrIdfyDict, designnum, partselectanalyzer, sigdiffStr_Refmax, sigdiffStr_Maxbit, isCond, preNode = None, info_op = None): pass

class DFTerminal(DFNode):
    attr_names = ('name',)
    def __init__(self, name):
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


        ret = '(Terminal '
        for n in self.name:
            ret += str(n) + '.'
        return ret[0:-1] + ')'

    def muxModify(self, newScopeName_list, dinbool=None, din_repeatedstr=None):#dinbool<-start from here, think har dim make the signal back to normal
        #check if "mux_template" exists in the name
        e0_scopechain = self.name.scopechain[0]
        if e0_scopechain.scopename == "mux_template":
            self.name.scopechain.remove(e0_scopechain)

            scopename_cpy = copy.deepcopy(newScopeName_list)

            if dinbool and self.name.scopechain[-1].scopename.startswith(din_repeatedstr):
                self.name.scopechain[-1].scopename = self.name.scopechain[-1].scopename[len(din_repeatedstr):]

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

    def traverse(self, preNode, sigDiff, muxIdfy, options, info_dict, info_op = None, info_str=None):
        self.preNode = preNode

        if not info_str:
            muxIdfy.constantNum = muxIdfy.constantNum + 1
        elif 'branch' in info_str:
            brIdfy = muxIdfy.brIdfyDict[preNode]
            brIdfy.constantNum = brIdfy.constantNum + 1


        ret = '(Constant ' + str(self.value) + ')'
        return ret

    def muxModify(self, newScopeName_list, dinbool=None, din_repeatedstr=None):
        return

class DFIntConst(DFConstant):
    def __init__(self, value):
        self.value = value
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

    def traverse(self, preNode, sigDiff, muxIdfy, options, info_dict, info_op = None, info_str=None):
        self.preNode = preNode

        if not info_str and \
                info_str != 'lsb' and info_str != 'msb' and \
                self.value != 0:
            muxIdfy.constantNum = muxIdfy.constantNum + 1

        elif 'branch' in info_str and self.value != 0:

            brIdfy = muxIdfy.brIdfyDict[preNode]
            brIdfy.constantNum = brIdfy.constantNum + 1

        ret = '(IntConst ' + str(self.value) + ')'
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
    def tostr(self):
        ret = '(FloatConst ' + str(self.value) + ')'
        return ret
    def eval(self):
        return float(self.value)

    def traverse(self, preNode, sigDiff, muxIdfy, options, info_dict, info_op = None, info_str=None):
        self.preNode = preNode

        if not info_str:
            muxIdfy.constantNum = muxIdfy.constantNum + 1

        elif 'branch' in info_str:
            brIdfy = muxIdfy.brIdfyDict[preNode]
            brIdfy.constantNum = brIdfy.constantNum + 1

        ret = '(FloatConst ' + str(self.value) + ')'
        return ret

class DFStringConst(DFConstant):
    def __init__(self, value):
        self.value = value
    def tostr(self):
        ret = '(StringConst ' + str(self.value) + ')'
        return ret
    def eval(self):
        return self.value

    def traverse(self, preNode, sigDiff, muxIdfy, options, info_dict, info_op = None, info_str=None):
        self.preNode = preNode

        ret = '(StringConst ' + str(self.value) + ')'
        return ret

################################################################################
class DFNotTerminal(DFNode): pass

class DFOperator(DFNotTerminal):
    attr_names = ('operator',)
    def __init__(self, nextnodes, operator):
        self.nextnodes = nextnodes
        self.operator = operator

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
        ret = ret[0:-1] + ')'
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

    def traverse(self, preNode, sigDiff, muxIdfy, options, info_dict, info_op = None, info_str=None):
        self.preNode = preNode

        ret = '(Partselect'
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

    def traverse(self, preNode, sigDiff, muxIdfy, options, info_dict, info_op = None, info_str=None):
        self.preNode = preNode

        ret = '(Pointer'
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

    def traverse(self, preNode, sigDiff, muxIdfy, options, info_dict, info_op = None, info_str=None):
        self.preNode = preNode

        ret = '(Concat'
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

    def traverse(self, preNode, sigDiff, muxIdfy, options, info_dict, info_op = None, info_str=None):
        self.preNode = preNode


        ret = '(Branch'
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

    def traverse(self, preNode, sigDiff, muxIdfy, options, info_dict, info_op = None, info_str=None):
        self.preNode = preNode

        return self.tostr()

class DFUndefined(DFNode):
    attr_names = ('width',)
    def __init__(self, width):
        self.width = width
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

    def traverse(self, preNode, sigDiff, muxIdfy, options, info_dict, info_op = None, info_str=None):
        self.preNode = preNode

        return self.tostr()

class DFHighImpedance(DFNode):
    attr_names = ('width',)
    def __init__(self, width):
        self.width = width
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

    def traverse(self, preNode, sigDiff, muxIdfy, options, info_dict, info_op = None, info_str=None):
        self.preNode = preNode

        return self.tostr()

################################################################################
class DFDelay(DFNotTerminal):
    attr_names = ()
    def __init__(self, nextnode):
        self.nextnode = nextnode
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


    def traverse(self, sigDiff, muxIdfy, options, info_dict, info_op = None, info_str=None):

        ret = '(Bind'
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
