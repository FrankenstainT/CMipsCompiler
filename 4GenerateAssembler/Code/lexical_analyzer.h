/*
lexical_analyzer.cpp
symbol table and lexical coding table
Get DFAs from given regular expressions with functions in lexical_tool.h
Identify words in the testing code by checking the DFAs one by one 
*/
#include<bits/stdc++.h>
#include "lexical_tool.h"
using namespace std;

// input element
struct inelm{
    string val,type;
    int id;
    pos p;
};

map<string,int> lct;// lexical coding table
vector<vector<DFAnode> > DFAs;
set<char> splitors,ins;
pair<int,int> isDFA(int k,int begin,vector<posc>cod){
    int cur=0;
    for(int i=begin;;++i){
        int f=0;
        for(auto it=DFAs[k][cur].nxt.begin();it!=DFAs[k][cur].nxt.end();++it){
            if(it->c==cod[i].c){
                cur=it->dst;
                f=1;
                break;
            }
        }
        if(!f){
            if(DFAs[k][cur].end)
                return pair<int,int>(0,i);
            else return pair<int,int>(1,i);
        }
    }
}
// build lexical coding table
void buildlct(){
    vector<string> lt;
    lt.push_back("auto");
    lt.push_back("break");
    lt.push_back("case");
    lt.push_back("char");
    lt.push_back("const");
    lt.push_back("continue");
    lt.push_back("default");
    lt.push_back("do");
    lt.push_back("double");
    lt.push_back("else");
    lt.push_back("enum");
    lt.push_back("extern");
    lt.push_back("float");
    lt.push_back("for");
    lt.push_back("goto");
    lt.push_back("if");
    lt.push_back("int");
    lt.push_back("long");
    lt.push_back("register");
    lt.push_back("return");
    lt.push_back("short");
    lt.push_back("signed");
    lt.push_back("sizeof");
    lt.push_back("static");
    lt.push_back("struct");
    lt.push_back("switch");
    lt.push_back("typedef");
    lt.push_back("union");
    lt.push_back("unsigned");
    lt.push_back("void");
    lt.push_back("volatile");
    lt.push_back("while");
    lt.push_back("inline");
    lt.push_back("restrict");
    lt.push_back("_Bool");
    lt.push_back("_Complex");
    lt.push_back("_Imaginary");
    lt.push_back("_Alignas");
    lt.push_back("_Alignof");
    lt.push_back("_Atomic");
    lt.push_back("_Static_assert");
    lt.push_back("_Noreturn");
    lt.push_back("_Thread_local");
    lt.push_back("_Generic");
    lt.push_back(",");
    lt.push_back(";");
    lt.push_back(":");
    lt.push_back("{");
    lt.push_back("}");
    lt.push_back("\\a");
    lt.push_back("\\b");
    lt.push_back("\\f");
    lt.push_back("\\n");
    lt.push_back("\\r");
    lt.push_back("\\t");
    lt.push_back("\\v");
    lt.push_back("\\\\");
    lt.push_back("\\'");
    lt.push_back("\\\"");
    lt.push_back("\\?");
    lt.push_back("\\0");
    lt.push_back("\\ddd");
    lt.push_back("\\xhh");
    lt.push_back("(");
    lt.push_back(")");
    lt.push_back("+");
    lt.push_back("-");
    lt.push_back("*");
    lt.push_back("/");
    lt.push_back(".");
    lt.push_back("=");
    lt.push_back("&");
    lt.push_back("|");
    lt.push_back("^");
    lt.push_back("%");
    lt.push_back("<");
    lt.push_back(">");
    lt.push_back("~");
    lt.push_back("!");
    lt.push_back("[");
    lt.push_back("]");
    lt.push_back("->");
    lt.push_back("++");
    lt.push_back("--");
    lt.push_back("<<");
    lt.push_back(">>");
    lt.push_back("<=");
    lt.push_back(">=");
    lt.push_back("==");
    lt.push_back("!=");
    lt.push_back("&&");
    lt.push_back("||");
    lt.push_back("?=");
    lt.push_back("+=");
    lt.push_back("-=");
    lt.push_back("*=");
    lt.push_back("/=");
    lt.push_back("%=");
    lt.push_back("&=");
    lt.push_back("^=");
    lt.push_back("|=");
    lt.push_back("<<=");
    lt.push_back(">>=");
    lt.push_back("'");
    lt.push_back("\"");
    lt.push_back("id");
    lt.push_back("decimal");
    lt.push_back("float_const");
    lt.push_back("hex");
    lt.push_back("#");
    for(int i=1;i<=lt.size();++i){
        lct[lt[i-1]]=i;
    }
}
vector<inelm> inputs;
void print1(string s,int begin,int end,vector<posc>cod){
    inelm ine;
    ine.type=s;
    //cout << s;
    //printf("(%d), '",lct[s]);
    ine.id=lct[s];
    ine.p=cod[begin].p;
    for(int k=begin;k<end;++k){
        //printf("%c",cod[k].c);
        ine.val+=cod[k].c;
    }//printf("'>\n");
    inputs.push_back(ine);
}

void inpts(char fn[]){
    //char fn[]="aplusb.c";
    string re;
    //printf("Please input the number of regular expressions:(Finish your input by Enter)");
    int n=7;
    //scanf("%d",&n);
    //printf("The sequence of matching words to tokens depends on the sequence in which the regular expressions are inputed.\n");
    //printf("Please input %d regular expressions:\n",n);
    /*vector<string> tips;
    tips.push_back("Please input the regular expression for key words:");
    tips.push_back("Please input the regular expression for float constant:");
    tips.push_back("Please input the regular expression for decimal integer constant:");
    tips.push_back("Please input the regular expression for hexadecimal integer constant:");
    tips.push_back("Please input the regular expression for identifiers:");
    tips.push_back("Please input the regular expression for delimiters:");
    tips.push_back("Please input the regular expression for operators:");
    *//*cin >> re;
    cout << ShuntingYard(re) << endl;*/
    //for(int i=0;i<1;++i){
        //cin >> re;*/
        /*string rep=ShuntingYard(re);
        cout <<rep<<endl;*/
        //subNFA nfa=Thompson(rep);
        //re="(A|B|C|D|E|F|G|H|I|J|K|L|M|N|O|P|Q|R|S|T|U|V|W|X|Y|Z|a|b|c|d|e|f|g|h|i|j|k|l|m|n|o|p|q|r|s|t|u|v|w|x|y|z|\\_)_(A|B|C|D|E|F|G|H|I|J|K|L|M|N|O|P|Q|R|S|T|U|V|W|X|Y|Z|a|b|c|d|e|f|g|h|i|j|k|l|m|n|o|p|q|r|s|t|u|v|w|x|y|z|\\_|0|1|2|3|4|5|6|7|8|9)*";
        //printnfa(nfa);
        /*re="((\\+|-)|\\e)_((1|2|3|4|5|6|7|8|9)_(0|1|2|3|4|5|6|7|8|9)*|0)";
        /*vector<DFAnode> aDFA=getDFA(re);
        printDFA(aDFA);
        //DFAs.push_back(aDFA);
    }*/
    vector<string> ress;
    ress.push_back("a_u_t_o|b_r_e_a_k|c_a_s_e|c_h_a_r|c_o_n_s_t|c_o_n_t_i_n_u_e|d_e_f_a_u_l_t|d_o|d_o_u_b_l_e|e_l_s_e|e_n_u_m|e_x_t_e_r_n|f_l_o_a_t|f_o_r|g_o_t_o|i_f|i_n_t|l_o_n_g|r_e_g_i_s_t_e_r|r_e_t_u_r_n|s_h_o_r_t|s_i_g_n_e_d|s_i_z_e_o_f|s_t_a_t_i_c|s_t_r_u_c_t|s_w_i_t_c_h|t_y_p_e_d_e_f|u_n_i_o_n|u_n_s_i_g_n_e_d|v_o_i_d|v_o_l_a_t_i_l_e|w_h_i_l_e|i_n_l_i_n_e|r_e_s_t_r_i_c_t|\\__B_o_o_l|\\__C_o_m_p_l_e_x|\\__I_m_a_g_i_n_a_r_y|\\__A_l_i_g_n_a_s|\\__A_l_i_g_n_o_f|\\__A_t_o_m_i_c|\\__S_t_a_t_i_c_\\__a_s_s_e_r_t|\\__N_o_r_e_t_u_r_n|\\__T_h_r_e_a_d_\\__l_o_c_a_l|\\__G_e_n_e_r_i_c");
    ress.push_back("((\\+|-)|\\e)_(0|1|2|3|4|5|6|7|8|9)*_._(0|1|2|3|4|5|6|7|8|9)*_(((e|E)_((\\+|-)|\\e)_(0|1|2|3|4|5|6|7|8|9)_(0|1|2|3|4|5|6|7|8|9)*)|\\e)");
    ress.push_back("(1|2|3|4|5|6|7|8|9)_(0|1|2|3|4|5|6|7|8|9)*|0");
    ress.push_back("0_x_(0|1|2|3|4|5|6|7|8|9|A|B|C|D|E|F|a|b|c|d|e|f)_(0|1|2|3|4|5|6|7|8|9|A|B|C|D|E|F|a|b|c|d|e|f)*");
    ress.push_back("(A|B|C|D|E|F|G|H|I|J|K|L|M|N|O|P|Q|R|S|T|U|V|W|X|Y|Z|a|b|c|d|e|f|g|h|i|j|k|l|m|n|o|p|q|r|s|t|u|v|w|x|y|z|\\_)_(A|B|C|D|E|F|G|H|I|J|K|L|M|N|O|P|Q|R|S|T|U|V|W|X|Y|Z|a|b|c|d|e|f|g|h|i|j|k|l|m|n|o|p|q|r|s|t|u|v|w|x|y|z|\\_|0|1|2|3|4|5|6|7|8|9)*");
    ress.push_back(",|;|:|{|}|'|\"|#");
    ress.push_back("\\(|\\)|\\+|-|\\*|/|.|=|&|\\||^|%|<|>|~|!|[|]|-_>|\\+_\\+|-_-|<_<|>_>|<_=|>_=|=_=|!_=|&_&|\\|_\\||?_:|\\+_=|-_=|\\*_=|/_=|%_=|&_=|^_=|\\|_=|<_<_=|>_>_=");
    set<char> splt;
    splt=getchars(ress[5]);
    set_union(splitors.begin(),splitors.end(),splt.begin(),splt.end(),inserter(splitors,splitors.begin()));
    splt=getchars(ress[6]);
    set_union(splitors.begin(),splitors.end(),splt.begin(),splt.end(),inserter(splitors,splitors.begin()));
    splitors.insert('\n');
    splitors.insert(' ');
    splitors.insert('\t');
    ins=splitors;
    ins.erase('.');
    //printset(splitors);
    for(int i=0;i<n;++i){
        vector<DFAnode> aDFA=getDFA(ress[i]);
        DFAs.push_back(aDFA);
    }
    vector<posc> cod=getcode(fn);
    for(int i=0;i<cod.size();++i){
        if(cod[i].c=='\0'){
            printf("Lexical analysis finished!\n");
            break;
        }
        if(cod[i].c!=' '&&cod[i].c!='\n'&&cod[i].c!='\t'){
            int maxi=i;
            bool suc=false;
            for(int j=0;j<n;++j){
                //if(j==0)printDFA(DFAs[j]);
                pair<int,int> res=isDFA(j,i,cod);
                if(!res.first){
                    switch(j){
                        case 1:
                            if(splitors.count(cod[res.second].c)){
                                //printf("<");
                                print1("float_const",i,res.second,cod);
                                suc=true;
                            }else{
                                if(res.second>maxi){
                                    maxi=res.second;
                                }
                            }    
                            break;
                        case 2:
                            if(ins.count(cod[res.second].c)){
                                //printf("<");
                                print1("decimal",i,res.second,cod);
                                suc=true;
                            }else{
                                if(res.second>maxi){
                                    maxi=res.second;
                                }
                            }
                            break;
                        case 3:
                            if(ins.count(cod[res.second].c)){
                                //printf("<");
                                print1("hex",i,res.second,cod);
                                suc=true;
                            }else{
                                if(res.second>maxi){
                                    maxi=res.second;
                                }
                            }
                            break;
                        case 4:
                            if(splitors.count(cod[res.second].c)){
                                //printf("<");
                                print1("id",i,res.second,cod);
                                /*symt_attr sym;
                                sym.p=cod[i].p;
                                string symval;
                                for(int j=i;j<res.second;++j){
                                    symval.push_back(cod[j].c);
                                }
                                symt[symval]=sym;*/
                                suc=true;
                            }else{
                                if(res.second>maxi){
                                    maxi=res.second;
                                }
                            }
                            break;
                        default:
                            string s;
                            //printf("<");
                            for(int k=i;k<res.second;++k){
                                s.push_back(cod[k].c);
                            }//cout << s;
                            inelm ine;
                            ine.type=s;
                            ine.id=lct[s];
                            //printf("(%d), '---'>\n",lct[s]);
                            ine.val="---";
                            ine.p=cod[i].p;
                            inputs.push_back(ine);
                            suc=true;
                            break;
                    }
                    if(suc){
                        i=res.second-1;
                        break;
                    }
                }
            }
            if(!suc){
                printf("LEXICAL ERROR at Ln %d, Col %d! \"",cod[i].p.line,cod[i].p.column);
                int j;
                for(j=maxi+1;!ins.count(cod[j].c)&&cod[j].c!='\0';++j);
                maxi=j-1;
                for(int j=i;j<=maxi;++j){
                    printf("%c",cod[j].c);
                }printf("\" can't be identified!\n");
                i=maxi;
            }
        }  
    }
    /*printf("Symbol Table:\n");
    for(auto it=symt.begin();it!=symt.end();++it){
        cout << it->val << ' ' << it->p.line << ',' << it->p.column << endl;
    }*/
    //printDFA(DFAs[0]);
    //system("pause");
    //return 0;
    inelm end;
    end.val=end.type="$";
    inputs.push_back(end);
    //return inputs;
}