#include<bits/stdc++.h>
#include "lexical_analyzer.h"
#define tn 10000
map<string,vector<vector<string> > > grammars; // the given grammars
map<vector<string>, set<string> > FIRST; // FIRST sets
map<string, set<string> > FOLLOW,FD;// FOLLOW sets, FOLLOW DEPENDENCY
map<pair<string,string>,vector<string> > ppt; // predictive parsing table
set<string> terminal,nonterminals;// terminal symbols and nonterminals in the given grammars
char fn[]="inputs.c";// source file name
vector<int> id_val;// values of identifiers
// symbol table node
map<string,set<string> > struct_table;// id name -> struct names
struct symt_attr{
    string type;
    pos p;
    int val,addr;
    symt_attr(){type="unknown";}
    symt_attr(string type,pos p,int addr):type(type),p(p),addr(addr){}
};
struct grmsym{// grammar symbol
    string first;// symbol
    int second;// node number in tree
    string type;// type for identifier
    grmsym(string f,int s):first(f),second(s){type="unknown";}
};
struct node{
    string sname,iname,stype,itype;
    int sval,ival,id,par,saddr,iaddr;// value, id, parent id, address for value
    vector<int> neibs;// children neighbors
    pos ip,sp;// postion in source file for reporting problems
    node(){itype=stype="unknown";}
    node(string na,int id):sname(na),id(id){itype="unknown";stype="unknown";}
};
map<string,symt_attr> symtable;// symbol table
node gptree[tn];// grammar parsing tree

void getFS(set<string>& s, vector<vector<string> >::iterator prd);

// print vector<string>
void printVS(const vector<string>& body){
    for(auto sym=body.begin();sym!=body.end();++sym){
        cout << ' ' << *sym;
    }
}

// judge whether a string s is null("\177")
bool isnull(const string& s){
    return s.size()==1&&s[0]==127;
}

// show FIRST sets
void printFIRST(){
    /* test FIRST*/
    printf("FIRST:\n");
    for(auto sys=FIRST.begin();sys!=FIRST.end();++sys){
        printf("FIRST(");
        printVS(sys->first);
        printf(" )={ ");
        printset(sys->second);
        printf("}\n");
    }
}

set<string> getF(const string& X){
    /*
    Return FIRST(X) for grammar symbol X.
    */
    vector<string> F;
    set<string> s;
    F.push_back(X);
    if(isnull(X)){
        s.insert(X);
        return FIRST[F]=s;
    }
    if(lct.count(X)||isnull(X)){
        s.insert(X);
        return FIRST[F]=s;
    }
    if(FIRST.count(F))return FIRST[F];
    for(auto prd = grammars[X].begin();prd!=grammars[X].end();++prd){
        getFS(s,prd);
    }
    return FIRST[F]=s;
}

// calculate FIRST(*prd) and store it in to s
void getFS(set<string>& s,vector<vector<string> >::iterator prd){
    for(auto sym = prd->begin();sym!=prd->end();++sym){
        string null(1,127),symt=*sym;
        set<string> ft=getF(symt),ft1=ft;
        ft.erase(null);
        set_union(s.begin(),s.end(),ft.begin(),ft.end(),inserter(s,s.begin()));
        if(!ft1.count(null)){
            break;
        }
        if(sym==--prd->end()){
            s.insert(null);
        }
    }
}

void getFIRST(){
    /* get FIRST for every productions in the given grammars */
    for(auto prod=grammars.begin();prod!=grammars.end();++prod){
        for(auto body=prod->second.begin();body!=prod->second.end();++body){
            getFS(FIRST[*body],body);
        }
    }
}

// get FOLLOW sets for all the nonterminals in the given grammars
void getFOLLOW(){
    FOLLOW["S"].insert("$");
    //printf("\n\nBegin getFOLLOW!\n\n");
    for(auto prd=grammars.begin();prd!=grammars.end();++prd){
        for(auto body = prd->second.begin();body!=prd->second.end();++body){
            for(int si=0;si<body->size();++si){
                if(!lct.count((*body)[si])){
                    for(int j=si+1;j<body->size();++j){
                        string tj=(*body)[j];
                        set<string> ft=getF(tj);            
                        string null(1,127);
                        ft.erase(null);
                        set_union(FOLLOW[(*body)[si]].begin(),
                            FOLLOW[(*body)[si]].end(),ft.begin(),
                            ft.end(),inserter(FOLLOW[(*body)[si]],
                            FOLLOW[(*body)[si]].begin()));
                        if(!getF(tj).count(null)){
                            break;
                        }
                        if(j==body->size()-1){
                            FD[(*body)[si]].insert(prd->first);
                        }
                    }
                    if(si==body->size()-1){
                        FD[(*body)[si]].insert(prd->first);
                    }
                }
            }
        }
    }
    while(true){
        int bk=0;
        for(auto sym=FD.begin();sym!=FD.end();++sym){
            int os=FOLLOW[sym->first].size();
            for(auto sd=sym->second.begin();sd!=sym->second.end();++sd){
                set_union(FOLLOW[sym->first].begin(),FOLLOW[sym->first].end(),
                    FOLLOW[*sd].begin(),FOLLOW[*sd].end(),
                    inserter(FOLLOW[sym->first],FOLLOW[sym->first].begin()));
            }
            if(FOLLOW[sym->first].size()>os){
                ++bk;
            }
        }
        if(bk==0)break;
    }
}

void printFOLLOW(){
    /*show FOLLOW sets, only for test*/
    printf("FOLLOW:\n");
    for(auto sym=FOLLOW.begin();sym!=FOLLOW.end();++sym){
        cout << "FOLLOW(" << sym->first << ") = { ";
        printset(sym->second);
        printf("}\n");
    }
}

void getGrammars(){
    /*
    Receive grammars from standard input stream and save it in grammars.
    */
    printf("Please input grammars(ended with \"end\"):\n");
    while(true){
        string prod;
        getline(cin,prod);
        string t,head;
        istringstream iss(prod);
        int i=0;
        vector<vector<string> > prods;
        vector<string> body;
        while(iss >> t){
            if(i==0){
                if(t=="end")return;
                head = t;
                ++i;
            }else{
                if(t=="|"){
                    prods.push_back(body);
                    body.clear();
                }else{
                    if(t=="\\e"){
                        t=127;
                    }else{
                        t.erase(remove(t.begin(),t.end(),'\\'),t.end());
                    }
                    body.push_back(t);
                }
            }
        }
        if(!prod.empty()){
            prods.push_back(body);
            grammars[head]=prods;
        }
        
    }
}

// show the Grammars the program got, only for test
void printGrammars(){
    for(auto it=grammars.begin();it!=grammars.end();++it){
        cout << it->first << " ->";
        for(auto body=(it->second).begin();body!=(it->second).end();++body){
            if(body!=(it->second).begin()){
                printf(" |");
            }
            printVS(*body);
        }
        cout << endl;
    }
}

void getPPT(){
    /* get predictive parsing table*/
    for(auto prd=grammars.begin();prd!=grammars.end();++prd){
        for(auto body=prd->second.begin();body!=prd->second.end();++body){
            set<string> fA=FIRST[*body];
            string null(1,127);
            for(auto nsym=fA.begin();nsym!=fA.end();++nsym){
                if(*nsym!=null){
                    pair<string,string> pk;
                    pk.first=prd->first;
                    pk.second=*nsym;
                    ppt[pk]=*body;
                }else{
                    set<string> fF=FOLLOW[prd->first];
                    for(auto sym=fF.begin();sym!=fF.end();++sym){
                        if(*sym!=null){
                            pair<string,string>pk;
                            pk.first=prd->first;
                            pk.second=*sym;
                            ppt[pk]=*body;
                        }
                    }
                }
            }
        }
    }
    // deal with Error type
    vector<string> err(2);
    err[0]="Error!";
    err[1]="Operator lost!";
    ppt[pair<string,string>("7","decimal")]=err;
    ppt[pair<string,string>("7","id")]=err;
    err[1]="Operand lost!";
    ppt[pair<string,string>("J",")")]=err;
    ppt[pair<string,string>("K",")")]=err;
    ppt[pair<string,string>("I",")")]=err;
    ppt[pair<string,string>("H",")")]=err;
    ppt[pair<string,string>("M",")")]=err;
    ppt[pair<string,string>("L",")")]=err;
    ppt[pair<string,string>("G",")")]=err;
    ppt[pair<string,string>("expr",")")]=err;
}

void getSym(){
    /* get terminal symbols set and nonterminals set*/
    for(auto prd=grammars.begin();prd!=grammars.end();++prd){
        nonterminals.insert(prd->first);
        for(auto body=prd->second.begin();body!=prd->second.end();++body){
            for(auto sym=body->begin();sym!=body->end();++sym){
                terminal.insert(*sym);
            }
        }
    }
    terminal.insert("$");
}

// show predictive parsing table, only used for test
void printPPT(){
    getSym();
    cout << "------------------------------------------------------------------------------------------------------------" << endl;
    cout << setiosflags(ios::left) << setw(3) << "             " << 
        resetiosflags(ios::left);
    for(auto ter=terminal.begin();ter!=terminal.end();++ter){
        cout << setiosflags(ios::left) << setw(8) << setfill(' ') << *ter << resetiosflags(ios::left);
    }cout << endl;
    cout << "------------------------------------------------------------------------------------------------------------" << endl;
    for (auto nt=nonterminals.begin();nt!=nonterminals.end();++nt) {
        cout << setiosflags(ios::left) << setw(3) << *nt << resetiosflags(ios::left);
        for(auto ter=terminal.begin();ter!=terminal.end();++ter){
            pair<string,string> pk;
            pk.first=*nt;
            pk.second=*ter;
            cout << setiosflags(ios::left) << setw(7) << setfill(' ') << ' ';
            if(*ter=="id"){
                printf("     ");
            }
            printVS(ppt[pk]);

            cout << resetiosflags(ios::left);
        }cout << endl;
    }
    cout << "------------------------------------------------------------------------------------------------------------" << endl;
    printf("%d %d %d %d %d\n",
        ppt[pair<string,string>("S'",")")]==vector<string>(1,"\177"),
        ppt[pair<string,string>("S'","$")]==vector<string>(1,"\177"),
        ppt[pair<string,string>("T'","$")]==vector<string>(1,"\177"),
        ppt[pair<string,string>("T'",")")]==vector<string>(1,"\177"),
        ppt[pair<string,string>("T'","+")].size());
}

stack<grmsym> St; // stack for LL1

/* generate parse tree node and put it into file*/
void genNode(ofstream& tree,const string& label,const int n){
    gptree[n].sname = label;
    gptree[n].id = n;
    char node[20];
    string fmt("node%d"),label1="\""+label+"\"";
    snprintf(node,sizeof(node),fmt.c_str(),n);
    tree << "   " << string(node) << "[label="<<label1<<"];" << endl;
}

/* generate parse tree edge and put it into file*/
void genEdge(ofstream& tree,int r,int cur){
    gptree[r].neibs.push_back(cur);
    gptree[cur].par=r;
    char node[20];
    string fmt("node%d");
    snprintf(node,sizeof(node),fmt.c_str(),r);
    tree << "   " << string(node) << "->" ;
    snprintf(node,sizeof(node),fmt.c_str(),cur);
    tree << string(node) << ";" << endl;
}
bool isnum(string &s){
    for(auto it=s.begin();it!=s.end();++it){
        if(!(*it>='0'&&*it<='9')){
            return false;
        }
    }
    return true;
}
void actions(int act, node& cur){
    node* pare=&gptree[cur.par];
    switch(act) {
        case 1:// check and fill the symbol table, check type
            if(symtable.count(gptree[pare->neibs[0]].sname)){  
                printf("%s:%d:%d: error: conflicting declaration '%s %s'\n",
                 fn, gptree[pare->neibs[0]].sp.line,
                 gptree[pare->neibs[0]].sp.column,
                 gptree[pare->neibs[0]].stype.c_str(),
                 gptree[pare->neibs[0]].sname.c_str());
            }else{
                gptree[pare->neibs[0]].saddr = id_val.size();
                id_val.push_back(0);// default 0 for id
                pare->stype = gptree[pare->neibs[0]].stype;
                gptree[pare->neibs[2]].iname = gptree[pare->neibs[0]].sname;
                gptree[pare->neibs[2]].itype = gptree[pare->neibs[0]].stype;
                if(symtable.count(pare->iname)&&symtable[pare->iname].type=="struct"){
                    if(struct_table.count(gptree[pare->neibs[0]].sname)){
                        printf("%s:%d:%d: note: conflicting field declaration '%s %s' with struct",
                            fn, gptree[pare->neibs[0]].sp.line,
                            gptree[pare->neibs[0]].sp.column,
                            gptree[pare->neibs[0]].stype.c_str(),
                            gptree[pare->neibs[0]].sname.c_str());
                        for(auto it=struct_table[gptree[pare->neibs[0]].sname].begin();
                                it!=struct_table[gptree[pare->neibs[0]].sname].end();++it){
                            cout << ' ' << *it; 
                            if(it!=--struct_table[gptree[pare->neibs[0]].sname].end())printf(",");
                        }printf("!\n");
                    }
                    struct_table[gptree[pare->neibs[0]].sname].insert(pare->iname);
                }else{
                    symtable[gptree[pare->neibs[0]].sname]=
                        symt_attr(gptree[pare->neibs[0]].stype,
                        gptree[pare->neibs[0]].sp,gptree[pare->neibs[0]].saddr);
                }
            }
        break;
        case 2:
            gptree[pare->neibs[1]].stype="struct";
            if(symtable.count(gptree[pare->neibs[1]].sname)){
                printf("%s:%d:%d: error: conflicting declaration '%s %s'\n",
                 fn, gptree[pare->neibs[1]].sp.line,
                 gptree[pare->neibs[1]].sp.column,
                 gptree[pare->neibs[1]].stype.c_str(),
                 gptree[pare->neibs[1]].sname.c_str());
            }else{
                /*struct field actions*/
                symtable[gptree[pare->neibs[1]].sname]=
                    symt_attr(gptree[pare->neibs[1]].stype,
                    gptree[pare->neibs[1]].sp,-1);
                gptree[pare->neibs[4]].iname = gptree[pare->neibs[1]].sname;// no struct address
                //printf("%d\n",symtable.count(gptree[pare->neibs[1]].sname));
            }
        break;
        case 3:
            if(!symtable.count(gptree[pare->neibs[0]].sname)){
                printf("%s:%d:%d: error: '%s' was not declared in this scope\n", 
                fn, gptree[pare->neibs[0]].sp.line,gptree[pare->neibs[0]].sp.column,gptree[pare->neibs[0]].sname.c_str());
            }else{
                gptree[pare->neibs[0]].stype = symtable[gptree[pare->neibs[0]].sname].type;
                gptree[pare->neibs[0]].saddr = symtable[gptree[pare->neibs[0]].sname].addr;
            }
            pare->stype = gptree[pare->neibs[0]].stype;
            pare->sp = gptree[pare->neibs[0]].sp;
            pare->saddr = gptree[pare->neibs[0]].saddr;
        break;
        case 4:
            pare->sp = gptree[pare->neibs[0]].sp;
        break;
        case 5:
            gptree[pare->neibs[2]].itype = gptree[pare->neibs[0]].stype;
            gptree[pare->neibs[2]].iaddr = gptree[pare->neibs[0]].saddr;
            gptree[pare->neibs[2]].ip = gptree[pare->neibs[0]].sp;
        break;
        case 6:
            pare->stype = gptree[pare->neibs[2]].stype;
            pare->saddr = gptree[pare->neibs[2]].saddr;
            pare->sp = gptree[pare->neibs[0]].sp;
        break;
        case 7:
            pare->stype = gptree[pare->neibs[0]].stype;
            pare->sval = gptree[pare->neibs[0]].sval;
            pare->sp = gptree[pare->neibs[0]].sp;
            pare->saddr = gptree[pare->neibs[0]].saddr;
        break;
        case 8:
            if(pare->itype!=gptree[pare->neibs[1]].stype){
                printf("%s:%d:%d: note:  mismatched types '%s' and '%s'\n", 
                fn, gptree[pare->neibs[1]].sp.line,gptree[pare->neibs[1]].sp.column,
                pare->itype.c_str(),gptree[pare->neibs[1]].stype.c_str());
            }
            gptree[pare->neibs[3]].iaddr=id_val.size();
            if(gptree[pare->neibs[0]].sname=="=="){
                id_val.push_back(id_val[gptree[pare->neibs[1]].saddr]==id_val[pare->iaddr]);
                gptree[pare->neibs[3]].itype = "_Bool";
            }
            if(gptree[pare->neibs[0]].sname=="!="){
                id_val.push_back(id_val[gptree[pare->neibs[1]].saddr]!=id_val[pare->iaddr]);
                gptree[pare->neibs[3]].itype = "_Bool";
            }
            if(gptree[pare->neibs[0]].sname==">="){
                id_val.push_back(id_val[pare->iaddr]>=id_val[gptree[pare->neibs[1]].saddr]);
                gptree[pare->neibs[3]].itype = "_Bool";
            }
            if(gptree[pare->neibs[0]].sname=="<="){
                id_val.push_back(id_val[pare->iaddr]<=id_val[gptree[pare->neibs[1]].saddr]);
                gptree[pare->neibs[3]].itype = "_Bool";
            }
            if(gptree[pare->neibs[0]].sname=="<"){
                id_val.push_back(id_val[pare->iaddr]<id_val[gptree[pare->neibs[1]].saddr]);
                gptree[pare->neibs[3]].itype = "_Bool";
            }
            if(gptree[pare->neibs[0]].sname==">"){
                id_val.push_back(id_val[pare->iaddr]>id_val[gptree[pare->neibs[1]].saddr]);
                gptree[pare->neibs[3]].itype = "_Bool";
            }
            if(gptree[pare->neibs[0]].sname=="||"){
                id_val.push_back(id_val[pare->iaddr]||id_val[gptree[pare->neibs[1]].saddr]);
                gptree[pare->neibs[3]].itype = "_Bool";
            }
            if(gptree[pare->neibs[0]].sname=="&&"){
                id_val.push_back(id_val[pare->iaddr]&&id_val[gptree[pare->neibs[1]].saddr]);
                gptree[pare->neibs[3]].itype = "_Bool";
            }
            if(gptree[pare->neibs[0]].sname=="+"){
                if(pare->itype!="int"||gptree[pare->neibs[1]].stype!="int"){
                    printf("%s:%d:%d: note:  only int operands can participate in arithmetic operations\n",
                     fn, gptree[pare->neibs[1]].sp.line,gptree[pare->neibs[1]].sp.column);
                }
                id_val.push_back(id_val[pare->iaddr]+id_val[gptree[pare->neibs[1]].saddr]);
                gptree[pare->neibs[3]].itype = "int";
            }
            if(gptree[pare->neibs[0]].sname=="-"){
                if(pare->itype!="int"||gptree[pare->neibs[1]].stype!="int"){
                    printf("%s:%d:%d: note:  only int operands can participate in arithmetic operations\n",
                     fn, gptree[pare->neibs[1]].sp.line,gptree[pare->neibs[1]].sp.column);
                }
                id_val.push_back(id_val[pare->iaddr]-id_val[gptree[pare->neibs[1]].saddr]);
                gptree[pare->neibs[3]].itype = "int";
            }
            if(gptree[pare->neibs[0]].sname=="*"){
                if(pare->itype!="int"||gptree[pare->neibs[1]].stype!="int"){
                    printf("%s:%d:%d: note:  only int operands can participate in arithmetic operations\n",
                     fn, gptree[pare->neibs[1]].sp.line,gptree[pare->neibs[1]].sp.column);
                }
                id_val.push_back(id_val[pare->iaddr]*id_val[gptree[pare->neibs[1]].saddr]);
                gptree[pare->neibs[3]].itype = "int";
            }
            if(gptree[pare->neibs[0]].sname=="/"){
                if(pare->itype!="int"||gptree[pare->neibs[1]].stype!="int"){
                    printf("%s:%d:%d: note:  only int operands can participate in arithmetic operations\n",
                     fn, gptree[pare->neibs[1]].sp.line,gptree[pare->neibs[1]].sp.column);
                }
                id_val.push_back(id_val[pare->iaddr]/id_val[gptree[pare->neibs[1]].saddr]);
                gptree[pare->neibs[3]].itype = "int";
            }
            if(gptree[pare->neibs[0]].sname=="|"){
                id_val.push_back(id_val[pare->iaddr]|id_val[gptree[pare->neibs[1]].saddr]);
                gptree[pare->neibs[3]].itype = pare->itype;
            }
            if(gptree[pare->neibs[0]].sname=="&"){
                id_val.push_back(id_val[pare->iaddr]&id_val[gptree[pare->neibs[1]].saddr]);
                gptree[pare->neibs[3]].itype = pare->itype;
            }
        break;
        case 9:
            pare->stype = gptree[pare->neibs[3]].stype;
            pare->saddr = gptree[pare->neibs[3]].saddr;
        break;
        case 10:
            pare->stype = pare->itype;
            pare->saddr = pare->iaddr;
        break;
        case 11:
            gptree[pare->neibs[2]].iname=gptree[pare->neibs[0]].sname;
            gptree[pare->neibs[2]].ip=gptree[pare->neibs[0]].sp;
        break;
        case 12:
            if(symtable[pare->iname].type!=gptree[pare->neibs[1]].stype){
                printf("%s:%d:%d: error: conversion from '%s' to '%s' requested\n",
                fn,gptree[pare->neibs[0]].sp.line,gptree[pare->neibs[0]].sp.column,
                gptree[pare->neibs[1]].stype.c_str(),symtable[pare->iname].type.c_str());
            }else{
                id_val[symtable[pare->iname].addr]=id_val[gptree[pare->neibs[1]].saddr];
                printf("%s = %d\n",pare->iname.c_str(),id_val[gptree[pare->neibs[1]].saddr]);
            }
        break;
        case 13:
            if(!symtable.count(pare->iname)){
                printf("%s:%d:%d: error: '%s' was not declared in this scope\n",
                 fn, pare->ip.line,pare->ip.column,
                 pare->iname.c_str());
            }else{
                if(symtable[pare->iname].type!=gptree[pare->neibs[1]].stype){
                    printf("%s:%d:%d: error: conversion from '%s' to '%s' requested\n",
                    fn,gptree[pare->neibs[0]].sp.line,gptree[pare->neibs[0]].sp.column,
                    gptree[pare->neibs[1]].stype.c_str(),symtable[pare->iname].type.c_str());
                }else{
                    id_val[symtable[pare->iname].addr]=id_val[gptree[pare->neibs[1]].saddr];
                    printf("%s = %d\n",pare->iname.c_str(),id_val[gptree[pare->neibs[1]].saddr]);
                }
            }
        break;
        case 14:
            gptree[pare->neibs[1]].iname = pare->iname;
            gptree[pare->neibs[2]].iname = pare->iname;
        break;
        case 15:
            gptree[pare->neibs[2]].iname = pare->iname;
        break;
        case 16:
            gptree[pare->neibs[2]].iname = pare->iname;
            gptree[pare->neibs[1]].iname = pare->iname;
        break;
        default:break;
    }
}
void LL1(){
    /*
    LL1 method
    Construct the parse tree
    */
    printf("Begin to construct parse tree!\n");
    ofstream tree("Tree.txt");
    int n=0;
    St.push(grmsym(string("$"),-1));// node name, node number(id)
    St.push(grmsym(string("S"),0));
    tree << "digraph G{" << endl;
    grmsym X=St.top();
    genNode(tree,X.first,n);
    auto a=inputs.begin();
    while(X.first!="$"){
        if(X.first==a->type){// terminal symbal matched
            St.pop();
            if(X.first=="id"){
                gptree[X.second].sname = a->val;
                gptree[X.second].stype=X.type;
            }
            if(X.first == "decimal"){
                gptree[X.second].sval = atoi(a->val.c_str());
                gptree[X.second].saddr=id_val.size();// new addr
                gptree[X.second].stype = "int";
                id_val.push_back(gptree[X.second].sval);
            }
            gptree[X.second].sp=a->p;
            ++a;
        }else if(lct.count(X.first)){// terminal symbal unmatched
            if(X.first==")"){// ')' lost
                cout << "Semantic Error at Ln " << a->p.line << 
                ", Col " << a->p.column << "! ')' lost!" << endl;
                St.pop();
            }
            else{
                printf("SYNTAX ERROR at Ln %d, Col %d! Expected a \"",
                a->p.line,a->p.column);
                cout << X.first << "\", but got a \"" << a->type << 
                "\"!" << endl;
                // Panic-Mode Recovery
                ++a;
                continue;
            }
            if(a->type=="$"){
                printf("Ended with error!\n");
                break;
            }
        }else if(!ppt.count(pair<string,string>(X.first,a->type))){
            printf("SYNTAX ERROR at Ln %d, Col %d! Unexpected symbol \"",
            a->p.line,a->p.column);
            cout << a->type << "\"!" << endl;
            // Panic-Mode Recovery
            ++a;
            if(a->type=="$"){
                printf("Ended with error!\n");
                break;
            }
            continue;
        }else if(ppt.count(pair<string,string>(X.first,a->type))){
            vector<string> body=ppt[pair<string,string>(X.first,a->type)];
            if(body.front()=="Error!"){// caught established error 
                cout << "Semantic Error at Ln " << a->p.line << ", Col " 
                << a->p.column << "! " << body[1] << endl;
                if(body[1]=="Operand lost!"){
                    gptree[X.second].sp=a->p;
                    St.pop();
                }
                else{
                    ++a;
                    continue;
                }
                if(a->type=="$"){
                    printf("Ended with error!\n");
                    break;
                }
            }else{
                vector<grmsym> notp;
                for(auto sym=body.begin();sym!=body.end();++sym){
                    genNode(tree,*sym,++n);
                    genEdge(tree,X.second,n);
                    notp.push_back(grmsym(*sym,n));
                }
                if(X.first=="T"){// shortcut for T
                    notp[2].type=notp[1].first;
                }
                if(X.first=="decs"){// shortcut for X
                    notp[1].type=X.type;
                    notp[2].type=X.type;
                }
                if(X.first=="dec'"&&notp.size()>1){
                    notp[2].type=X.type;
                }
                if(X.first=="dec"){
                    notp[0].type=X.type;
                }
                St.pop();
                /* push symbols onto the stack in a reverse order*/
                for(auto sel=notp.rbegin();sel!=notp.rend();++sel){
                    if(sel->first!="\177")
                        St.push(*sel);
                }
            }
        }else{
            printf("Unknown SYNTAX ERROR at Ln %d, Col %d!\n");
        }
        X=St.top();
    }
    tree << "}" << endl;
    tree.close();
    printf("Finished constructing parse tree!\n");
}
void dfs(node& cur){
    int act=atoi(cur.sname.c_str());
    if(act){
        actions(act,cur);
    }
    for(int i=0;i<cur.neibs.size();++i){
        dfs(gptree[cur.neibs[i]]);
    }
}
void initialize(){
    /* 
    initialize the program
    including build lct, get inputs, Grammars, FIRST, FOLLOW and PPT
    */
    buildlct();
    
    inpts(fn);
    // test input sequence
    //printf("%d\n",inputs.size());
    /*for(auto it=inputs.begin();it!=inputs.end();++it){
        printf("<");
        cout << it->type;
        cout << '(' << it->id << "), \'" << it->val << "\'> "<< it->p.column << ',' << it->p.line << endl;
    }*/
    getGrammars();
    // test getGrammars
    //printGrammars();
    getFIRST();
    //printFIRST();
    getFOLLOW();
    //printFOLLOW();
    getPPT();
    // test getPPT
    //printPPT();
}
// print grammar parsing tree
void printTree(){
    queue<int> q;
    q.push(0);
    while(!q.empty()){
        int cur = q.front();
        q.pop();
        printf("%d",cur);
        for(int i=0;i<gptree[cur].neibs.size();++i){
            printf(" %d",gptree[cur].neibs[i]);
            q.push(gptree[cur].neibs[i]);
        }printf("\n");
    }
}
void drawNode(ofstream& tree, node& cur){
    char node[20];
    string fmt("node%d"),label1="\""+cur.sname+";stype=";
    snprintf(node,sizeof(node),fmt.c_str(),cur.id);
    tree << "   " << string(node) << "[label="<<label1<<cur.stype<<
    ";itype="<<cur.itype<< ";\"];" << endl;
    if(cur.id!=0){
        char node[20];
        string fmt("node%d");
        snprintf(node,sizeof(node),fmt.c_str(),cur.par);
        tree << "   " << string(node) << "->" ;
        snprintf(node,sizeof(node),fmt.c_str(),cur.id);
        tree << string(node) << ";" << endl;
    }
    for(int i=0;i<cur.neibs.size();++i){
        drawNode(tree,gptree[cur.neibs[i]]);
    }
}
void drawTree(){
    ofstream tree("Tree.txt");
    tree << "digraph G{" << endl;
    drawNode(tree,gptree[0]);
    tree << "}" << endl;
}

int main(){
    initialize();
    LL1();
    dfs(gptree[0]);
    //printVec(id_val);
    //drawTree();
    //printTree();
    system("pause");
    return 0;
}