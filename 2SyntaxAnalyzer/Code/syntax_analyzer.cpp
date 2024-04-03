#include<bits/stdc++.h>
#include "lexical_analyzer.h"

map<string,vector<vector<string> > > grammars; // the given grammars
map<vector<string>, set<string> > FIRST; // FIRST sets
map<string, set<string> > FOLLOW,FD;// FOLLOW sets, FOLLOW DEPENDENCY
map<pair<string,string>,vector<string> > ppt; // predictive parsing table
set<string> terminal,nonterminals;// terminal symbols and nonterminals in the given grammars
//vector<inelm> inputs; // input code stream for compiling

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
    printf("\n\nBegin getFOLLOW!\n\n");
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

stack<pair<string,int> > St; // stack for LL1

/* generate parse tree node and put it into file*/
void genNode(ofstream& tree,const string& label,const int n){
    char node[20];
    string fmt("node%d"),label1="\""+label+"\"";
    snprintf(node,sizeof(node),fmt.c_str(),n);
    tree << "   " << string(node) << "[label="<<label1<<"];" << endl;
}

/* generate parse tree edge and put it into file*/
void genEdge(ofstream& tree,int r,int cur){
    char node[20];
    string fmt("node%d");
    snprintf(node,sizeof(node),fmt.c_str(),r);
    tree << "   " << string(node) << "->" ;
    snprintf(node,sizeof(node),fmt.c_str(),cur);
    tree << string(node) << ";" << endl;
}

void LL1(){
    /*
    LL1 method
    Construct the parse tree
    */
    printf("Begin to construct parse tree!\n");
    ofstream tree("Tree.txt");
    int n=0;
    St.push(pair<string,int>("$",-1));
    St.push(pair<string,int>("S",0));
    tree << "digraph G{" << endl;
    pair<string,int> X("S",0);
    genNode(tree,X.first,n);
    auto a=inputs.begin();
    while(X.first!="$"){
        if(X.first==a->type){
            St.pop();
            ++a;
        }else if(lct.count(X.first)){
            printf("SYNTAX ERROR at Ln %d, Col %d! Expected a \"",a->p.line,a->p.column);
            cout << X.first << "\", but got a \"" << a->type << "\"!" << endl;
            // Panic-Mode Recovery
            ++a;
            if(a->type=="$"){
                printf("Ended with error!\n");
                break;
            }
            continue;
        }else if(!ppt.count(pair<string,string>(X.first,a->type))){
            printf("SYNTAX ERROR at Ln %d, Col %d! Unexpected symbol \"",a->p.line,a->p.column);
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
            vector<pair<string,int>> notp;
            for(auto sym=body.begin();sym!=body.end();++sym){
                genNode(tree,*sym,++n);
                genEdge(tree,X.second,n);
                notp.push_back(pair<string,int>(*sym,n));
            }
            St.pop();
            /* push symbols onto the stack in a reverse order*/
            for(auto sel=notp.rbegin();sel!=notp.rend();++sel){
                if(sel->first!="\177")
                    St.push(*sel);
            }
        }else{
            printf("Unknown SYNTAX ERROR at Ln %d, Col %d!\n");
        }
        X=St.top();
    }
    tree << "}" << endl;
    printf("Finished constructing parse tree!\n");
}

void initialize(){
    /* 
    initialize the program
    including build lct, get inputs, Grammars, FIRST, FOLLOW and PPT
    */
    buildlct();
    char fn[]="inputs.c";
    inpts(fn);
    // test input sequence
    //printf("%d\n",inputs.size());
    /*for(auto it=inputs.begin();it!=inputs.end();++it){
        printf("<");
        cout << it->type;
        cout << '(' << it->id << "), \'" << it->val << "\'> "<< it->p.column << ',' << it->p.line << endl;
    }*/
    /*test getGrammars*/
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

int main(){
    initialize();
    LL1();
    system("pause");
    return 0;
}