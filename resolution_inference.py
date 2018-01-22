
#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Tue Nov  7 15:43:55 2017

@author: Sanjana
"""
import ply.lex as lex
import re
import copy
tokens = (
    'PREDICATE',
    'VARIABLE',
    'AND',
    'OR',
    'NOT',
    'IMPLIES',
    'LPAREN',
    'RPAREN',
    'CONSTANT'
)


t_AND = r'\&'
t_OR = r'\|'
t_NOT = r'\~'
t_VARIABLE = r'[a-z0-9]+'
t_PREDICATE = r'[A-Za-z]+\(.*?\)'
t_IMPLIES = r'=>'
t_LPAREN = r'\( '
t_RPAREN = r' \)'
t_CONSTANT = r'\w+'



def t_NUMBER(t):
    r'\d+'
    t.value = int(t.value)
    return t


t_ignore = " \t"

def t_newline(t):
    r'\n+'
    t.lexer.lineno += t.value.count("\n")
    
#checks for a given input, predicates should be of the given format
#example:a[x] is not a valid predicate representation
def t_error(t):
    print("Illegal character '%s'" % t.value[0])
    t.lexer.skip(1)



lexer= lex.lex()
 
#gives the list of arguments inside the predicate    
def getParameterList(predicate):
    return (predicate[predicate.find('(') + 1:predicate.find(')')]).split(',')


#provides the type of arguments, it's value and position given a predicate
def parametersfromPredicate(predicateArguments):
    arglist=[]
    for i in predicateArguments:
        lexer.input(i)
        while True:
            tok = lexer.token()
            if tok is None:
                break  
            arglist.append((tok.value, tok.type, tok.lexpos))
    return arglist


predicate_dict = {}


def mapSentencetoDict(sentence,lineno):
    #for any sentence in KB, it's predicates are added to dict with key=predicate and it's value the sentence line ,wherever it appears in KB
   
    lexer.input(sentence)
    Not = False
    while True:
        tok = lexer.token()
        if not tok:
            break  
       
        if tok.type == 'NOT':
            Not = True
        elif tok.type == 'PREDICATE':
            if Not:
                tok.value = "~"+tok.value
                Not = False
            if tok.value in predicate_dict:
                if lineno not in predicate_dict[tok.value]:
                    l = predicate_dict[tok.value]
                    l.append(lineno)
                    predicate_dict[tok.value] = l
            else:
                predicate_dict[tok.value] = [lineno]

   
    return


#negation of query   
def negate_query(query):
    
    if "~" in query:
        query=query.replace("~","")
    else:
        query="~"+query
      
    return query    

def tautology_sentence(sentence):
    list_predicates = sentence.replace(" ", "").split("|")
    i = 0
    while i<len(list_predicates):
        predicate1 = list_predicates[i]
        j = i+1
        while j<len(list_predicates):
            predicate2 = list_predicates[j]
            if "~" in predicate1:
                if predicate1 == "~"+predicate2:
                    return True
            elif "~" in predicate2:
                if predicate2 == "~"+predicate1:
                    return True
            j = j + 1
        i = i + 1
    return False
  
      

   
    
#standardizing the variable name in the predicates
def variable_standardization(sentence,n):
    global type_dict
    
    
    sol=[]
    list_predicates=sentence.split("|")
    for each in list_predicates:
        arg_list=[]
        predicateParameters=parametersfromPredicate(getParameterList(each))
        for ( Value,Type, pos) in predicateParameters:
            if Type == 'VARIABLE':
                Value = Value+str(n)
                type_dict[Value]=Type
            if Type=='CONSTANT':
                type_dict[Value]=Type
                
            arg_list.append(Value)
            
        ArgsSentence = ", ".join(arg_list)
        sol.append(each.split("(")[0]+"("+ArgsSentence+")")
    return "|".join(sol)

#if the negated version of the query is in kb, it's line number is returned
def searchNegatedPredicate_kb(predicate,KB):
    result=[]
    
    predicate_search=copy.deepcopy(predicate)
    predicate_search=negate_query(predicate_search)
    
    predicate_search_name = predicate_search.split("(")[0]
    for key in KB.keys():
        sentence = KB[key]
        sentencePredicates=sentence.split("|")
        sentencePredicatesNames=[]
        for predicate in sentencePredicates:
            sentencePredicatesNames.append(predicate.replace(" ", "").split("(")[0])
        if predicate_search_name in sentencePredicatesNames:
            result.append(key)
    return result


#substitutes the variables in the predicate to it's value in substitution list
def substitution(sentence,sub_dic):
    result=[]
    
    p_list=sentence.split("|")
    for p in p_list:
        arg_p=getParameterList(p)
        keys=sub_dic.keys()
          
        #if common between the predicate arg and arg in unification list
        if(set(keys) & set(arg_p)):
            p_name=p.split("(")[0]
            sol=[]
            k=sub_dic.keys()
            for arg in arg_p:
                if(arg in k and  type_dict[arg]=='VARIABLE'):
                    sol.append( sub_dic[arg])
                elif( type_dict[arg]=='CONSTANT' ):  
                    sol.append(arg)
                else:
                    sol.append(arg)
            predicate=p_name + "("+",".join(sol)+")"        
            result.append(predicate)
            
        else:
            result.append(p)
        
    return "|".join(result)    
    
    

def cantwopredicatesUnify(p1,p2):
    #can unify if two predicate names are same,number of arguments are same and the constants in the predicates are not contradictory
    
    arg1parameters=getParameterList(p1)
    number_arguments1=len(arg1parameters)
    arg2parameters=getParameterList(p2)
    #number_arguments2=len(arg2parameters)
   # arglist1_parameters=parametersfromPredicate(arg1parameters)
    #arglist2_parameters=parametersfromPredicate(arg2parameters)  
    
   
    ans=True 
    i=0
    while (i< number_arguments1 and ans==True):
        
        var1=arg1parameters[i]
        var2=arg2parameters[i]
        
        
        if(type_dict[var1]=='CONSTANT' and type_dict[var2]=='CONSTANT' and var1!=var2):
            ans=False
           
        
        i+=1
       
            
    return ans

#checks unification possible for predicates, if possible, provides substitution list
def unification_Predicates(predicate1, predicate2):
    result ={}#substitution list
    
    arg1parameters=getParameterList(predicate1)
    arg2parameters=getParameterList(predicate2)
  
    i = 0
    while i < len(arg2parameters):
  
        val1=arg1parameters[i]
        val2=arg2parameters[i]
        if (type_dict[val1] == 'CONSTANT' and type_dict[val2] == 'VARIABLE'):
            if ( val2 in result.keys() and result[val2] != val1 ):
                return False,{}
            elif (val2 not in result.keys()):
                result[val2] = val1
        elif (type_dict[val1] == 'VARIABLE' and type_dict[val2] == 'CONSTANT'):
            if (val1 in result.keys() and result[val1] != val2):
                return False,{}
            elif (val1 not in result.keys()):
                result[val1] = val2
        elif( type_dict[val1] == 'VARIABLE' or type_dict[val2] == 'VARIABLE'):
             #handle for f(x,x,y) and f(x,z,z) this should be false
            
            """
            if ((val1 in result.keys() and result[val1]!= val2)or (val2 in result.keys() and result[val2]!=val1 )):
                return False,{}
           
            else:
            """
            result[val1] = val2
        elif (type_dict[val1] == 'CONSTANT' and type_dict[val2] == 'CONSTANT' and val1 != val2):
            return False,{}
        i = i + 1
     
    return True, result
#define copylist,copy dictionary if time complexity is too much    


def resolution(kb,query):
    global resolved
    global intermediate    
    #p1->query, p2->negated version from kb
    predicates_query = query.replace(" ","").split("|")
    negated_Predicate_Sentences_kb=[]
    for predicate in predicates_query:
        negated_Predicate_Sentences_kb.append(searchNegatedPredicate_kb(predicate,kb))
    if not negated_Predicate_Sentences_kb:
       return
     
   
    i = 0
    while i<len(predicates_query):
        p1 = predicates_query[i]
     
        p1_name = p1.split("(")[0]

        for negated_Predicate_Sentence in negated_Predicate_Sentences_kb:
           
            for j in negated_Predicate_Sentence:
                sentence_kb = kb[j]
                sentence_Predicates_kb = sentence_kb.replace(" ","").split("|")
               
                
                for p2 in sentence_Predicates_kb:
                    p2_name =  p2.split("(")[0]
                    if "~" in p1_name:
                       notp2 = p1_name.replace("~","")
                    else:
                        notp2 = "~"+p1_name
                 
                    if(notp2==p2_name):
                        
                        if  cantwopredicatesUnify(p1,p2) : 
                        
                        
                            unification_bool, sub_val = unification_Predicates(p1,p2)
                           
                            
                            if unification_bool:
                                new_copy_p1list=copy.deepcopy(predicates_query)
                                new_copy_p1list.remove(p1)
                                new_copy_p2list=copy.deepcopy(sentence_Predicates_kb  )
                                new_copy_p2list.remove(p2)
                               
                                newSentencePredicates = list(set(set(new_copy_p1list).union(new_copy_p2list)))
                              
                                if not newSentencePredicates:
                                    resolved = True
                                   
                                    return True
                                unifiedSentence = substitution("|".join(newSentencePredicates),sub_val)
                              
                                   

                                if (p1,  sentence_kb, p2) not in intermediate:
                                   
                                    if not tautology_sentence(unifiedSentence):
                                        intermediate.append((p1,  sentence_kb, p2))
                                        resolution(kb, unifiedSentence)
                                      
                              

                                if resolved:
                                    return
                                    
        i = i+1
    return

     

    
    

def output(query,kb):
    global kb_num
    global dict_key
    global intermediate
    global resolved
    list_kb=[]
    dict_kb={}
    

    
    for each in kb:
        sentence=variable_standardization(each,kb_num)
        list_kb.append(sentence)
        
        kb_num+=1   
  
    list_kb=sorted(list_kb,key=len)  
    for each in list_kb:
        dict_kb[dict_key]=each
        mapSentencetoDict(each,dict_key)
        dict_key+=1
    fo1 = open("output.txt", "w+")    
   
    for query in qlist:
        dict_kb_query={}
        intermediate=[]
        resolved=False 
        dict_kb_query=copy.deepcopy(dict_kb)
        query=negate_query(query)
        query=variable_standardization(query,dict_key)
        dict_kb_query[dict_key]=query
        intermediate.append(query)
        
        resolution(dict_kb_query,query)
        #print(resolved)
        sol=str(resolved).upper()
        fo1.write(str(sol)+"\n")
        
    return    


#to read the input from the file
#list of all queries
qlist=[]
#list of all statement to knowledge base
kblist=[]
kb_num=1 
dict_key=1
type_dict={}
with open('input.txt') as f:
    words = [word.strip() for word in f]
qno=int(words.pop(0))
for i in range(0,qno):
    qlist.append(words[i])
kbno=int(words[qno])
for i in words[qno+1:]:
    kblist.append(i)
    
output(qlist,kblist) 
 
       


