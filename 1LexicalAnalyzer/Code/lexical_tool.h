/*
lexical_tool.h
basical struct for NFA, DFA and char with position in code
Shunting Yard Algorithm, Thompson Algorithm and Subset Construction Algorithm
other tool functions
*/
#ifndef LEXICAL_TOOL_H
#define LEXICAL_TOOL_H
#include<iostream>
#include<cstdio>
#include<string>
#include<vector>
#include<set>
#include<stack>
#include<algorithm>
#include<queue>
#include<map>
#define eps 127
using namespace std;
struct edge{
	int dst;
	char c;
};
set<char> chars;
struct NFAnode{
	int id,v=0;
	vector<edge> nxt;
};
struct DFAnode{
	int id,end=0;
	vector<edge> nxt;
	set<int> states;
};
vector<DFAnode> DFA;
map<set<int>, int>D;
vector<NFAnode> NFA;
struct subNFA{
	int start,end;
};
struct pos{
    int line,column;
};
struct posc{
    char c;
    pos p;
};
// compare precedence of a and b, return a>=b
bool compre(char a,char b){
	char pre[5]={'*','_','|','('};
	if(b=='('){
		return false;
	}
	for(int i=0;pre[i]!=b;++i){
		if(pre[i]==a)return true;
	}
	if(a==b)return true;
	return false;
}
// Shunting Yard Algorithm
// receive regular expression(re) as parameter, return reverse Polish notation of re
string ShuntingYard(string& re){
	string rep;
	stack<char> st;
	set<char> op={'(',')','_','*','|'};
	int escape=0;
	for(int i=0;i<re.size();++i){
		if(escape){
			if(re[i]=='e'){
				rep.pop_back();
				rep.push_back(eps);
			}else{
				rep.push_back(re[i]);
			}
			escape=0;
		}else{
			if(re[i]=='\\'){
				rep.push_back(re[i]);
				escape=1;
				continue;
			}
			if(op.count(re[i])){
				if(re[i]==')'){
					char top='\0';
					while(!st.empty()){
						top=st.top();
						st.pop();
						if(top=='(')break;
						rep.push_back(top);
					}
					if(top!='('){
						printf("Error! No compared '(' to ')' in regular expression!\n");
					}
				}else{
					char top;
					while(!st.empty()){
						top=st.top();
						if(compre(top,re[i])){
							st.pop();
							rep.push_back(top);
						}else break;
					}
					st.push(re[i]);
				}
			}else{
				rep.push_back(re[i]);
			}
		}
	}
	while(!st.empty()){
		rep.push_back(st.top());
		st.pop();
	}	
	return rep;
}
// get sub NFA from a char
subNFA fc(char a){
	edge edg;
	edg.c=a;
	edg.dst=NFA.size()+1;
	NFAnode start,end;
	start.id=NFA.size();
	end.id=NFA.size()+1;
	start.nxt.push_back(edg);
	subNFA sub;
	sub.start=start.id;
	sub.end = end.id;
	NFA.push_back(start);
	NFA.push_back(end);
	return sub;
}
// from re to NFA
subNFA Thompson(string& re){
	set<char> op={'_','*','|'};
	stack<subNFA> st;
	int escape=0;
	//cout << re << endl;
	//printf("rep.size()=%d\n",re.size());
	for(int i=0;i<re.size();++i){
		if(escape){
			st.push(fc(re[i]));
			escape=0;
		}else{
			if(re[i]=='\\'){
				escape=1;
				continue;
			}
			if(op.count(re[i])){
				switch(re[i]){
					case '_':{
						if(st.size()<2){
							printf("Error! There are less than two operands for operator _.\n");
						}
						subNFA a,b,nsb;
						b=st.top();
						st.pop();
						a=st.top();
						st.pop();
						nsb.start = a.start;
						nsb.end = b.end;
						NFA[a.end].nxt.insert(NFA[a.end].nxt.end(),NFA[b.start].nxt.begin(),NFA[b.start].nxt.end());
						st.push(nsb);
						break;
						}
					case '|':{
						if(st.size()<2){
							printf("Error! There are less than two operands for operator |.\n");
						}
						subNFA a,b,nsb;
						b=st.top();
						st.pop();
						a=st.top();
						st.pop();
						NFAnode start,end;
						start.id=NFA.size();
						end.id=NFA.size()+1;
						edge sa,ae,sb,be;
						sa.c=eps;
						sa.dst=a.start;
						sb.c=eps;
						sb.dst=b.start;
						ae.c=eps;
						ae.dst=end.id;
						be.c=eps;
						be.dst=end.id;
						start.nxt.push_back(sa);
						start.nxt.push_back(sb);
						NFA[a.end].nxt.push_back(ae);
						NFA[b.end].nxt.push_back(be);
						NFA.push_back(start);
						NFA.push_back(end);
						nsb.start=start.id;
						nsb.end=end.id;
						st.push(nsb);
						break;
						}
					case '*':{
						if(st.size()<1){
							printf("Error! There are no operand for operator *.\n");
						}
						subNFA a,nsb;
						a=st.top();
						st.pop();
						NFAnode start,end;
						start.id=NFA.size();
						end.id=NFA.size()+1;
						edge se,ses,sa,ae;// start to end, sub end to start
						se.c=ses.c=sa.c=ae.c=eps;
						se.dst=end.id;
						ses.dst=a.start;
						sa.dst=a.start;
						ae.dst=end.id;
						start.nxt.push_back(sa);
						start.nxt.push_back(se);
						NFA[a.end].nxt.push_back(ses);
						NFA[a.end].nxt.push_back(ae);
						NFA.push_back(start);
						NFA.push_back(end);
						nsb.start=start.id;
						nsb.end=end.id;
						st.push(nsb);
						break;
						}
					default:printf("Wrong operator!\n");break;
				}
			}else{
				st.push(fc(re[i]));
			}
		}
	}
	return st.top();
}
void printnfa(subNFA& nfa){
	printf("NFA\n");
	queue<int> q;
	q.push(nfa.start);
	while(!q.empty()){
		int cur=q.front();
		q.pop();
		if(!NFA[cur].v){
			NFA[cur].v=1;
			printf("%d:\n",cur);
			for(int i=0;i<NFA[cur].nxt.size();++i){
				printf("%c %d\n",NFA[cur].nxt[i].c,NFA[cur].nxt[i].dst);
				if(!NFA[NFA[cur].nxt[i].dst].v){
					q.push(NFA[cur].nxt[i].dst);
				}
			}
		}
	}
}
// closures deep first search
void cssdfs(set<int>& states,int id){
	for(int i=0;i<NFA[id].nxt.size();++i){
		if(NFA[id].nxt[i].c==eps){
			if(!states.count(NFA[id].nxt[i].dst)){
				states.insert(NFA[id].nxt[i].dst);
				cssdfs(states,NFA[id].nxt[i].dst);
			}
		}
	}
}
// input state id in NFA; output its closure
set<int> closures(int id){
	set<int> states;	
	states.insert(id);
	cssdfs(states,id);
	return states;
}
// input state set in NFA; output its closure
set<int> closureT(set<int>& states){
	set<int> Tstates;
	for(auto it=states.begin();it!=states.end();++it){
		set<int> clo=closures(*it);
		set_union(clo.begin(),clo.end(),Tstates.begin(),Tstates.end(),inserter(Tstates,Tstates.begin()));
	}
	return Tstates;
}
// input state set and char; output the destination state set
set<int> moveTa(set<int> states,char a){
	set<int> nstates;
	for(auto it=states.begin();it!=states.end();++it){
		for(auto itt=NFA[*it].nxt.begin();itt!=NFA[*it].nxt.end();++itt){
			if(itt->c==a){
				nstates.insert(itt->dst);
			}
		}
	}
	return nstates;
}
// get char set of string rep
set<char> getchars(string& rep){
	int escape=0;
	set<char> chars,op={'_','|','*'};	
	for(int i=0;i<rep.size();++i){
		if(escape){
			chars.insert(rep[i]);
			escape=0;
		}else{
			if(rep[i]=='\\'){
				escape=1;
				continue;
			}
			if(!op.count(rep[i])){
				chars.insert(rep[i]);
			}
		}
	}
	return chars;
}
// print DFA
void printDFA(vector<DFAnode> DFA){
	printf("\nDFA\n");
	for(int i=0;i<DFA.size();++i){
		printf("id = %d states =",DFA[i].id);
		for(auto it=DFA[i].states.begin();it!=DFA[i].states.end();++it){
			printf(" %d",*it);
		}printf("\n");
		for(int j=0;j<DFA[i].nxt.size();++j){
			printf("%c %d\n",DFA[i].nxt[j].c,DFA[i].nxt[j].dst);
		}
	}
}
// sub set Construction algorithm
// s0, the start state
void subsetConstruction(int s0,subNFA nfa){
	set<int> clos0 = closures(s0);
	D[clos0]=0;
	int ti=0;// tag index
	DFAnode cs0;
	cs0.id=0;
	if(clos0.count(nfa.end)){
		cs0.end=1;
	}
	cs0.states=clos0;
	DFA.push_back(cs0);
	while(ti<DFA.size()){
		set<int> U;
		for(auto it=chars.begin();it!=chars.end();++it){
			set<int> moveti=moveTa(DFA[ti].states,*it);
			set<int> cmta=closureT(moveti);
			DFAnode nn;
			if(cmta.size()){
				if(!D.count(cmta)){
					nn.id=DFA.size();
					nn.states=cmta;
					D[cmta]=DFA.size();
					if(nn.states.count(nfa.end)){
						nn.end=1;
					}
					DFA.push_back(nn);		
				}else{
					nn=DFA[D[cmta]];
				}
				edge edg;
				edg.c=*it;
				edg.dst=nn.id;
				DFA[ti].nxt.push_back(edg);
			}	
		}
		++ti;
	}
}
template<typename T>
void printset(set<T>& a){
	for(auto it=a.begin();it!=a.end();++it){
		cout << *it << ' ';
	}printf("\n");
}
// getcode in file fn
vector<posc> getcode(char fn[]){
	FILE *fp=fopen(fn,"r");
    char c;
    int state0=0;
    char lc='\0';
    vector<posc> cod;
    int line=1,col=1;
    while((c=getc(fp))!=EOF){
        switch(state0){
            case 0:
                if(c=='/'&&lc=='/'){
					cod.pop_back();
                    state0=1;
                }else if(c=='*'&&lc=='/'){
					cod.pop_back();
                    state0=2;
                }else{
                    pos p;
                    p.line=line;
                    posc pc;             
                    /*if(lc=='/'){
                        p.column=col-1;
                        pc.p=p;
                        pc.c='/';
                        cod.push_back(pc);
                    };*/
                    p.column=col;
                    pc.p=p;
                    pc.c=c;
                    cod.push_back(pc);
                }   
                break;
            case 1:
                if(c=='\n'){
                    state0=0;
                }
                break;
            case 2:
                if(lc=='*'&&c=='/'){
                    state0=0;
                    c='\0';
                }break;
            default:break;
        }
        lc=c;
        ++col;
        if(c=='\n'){
            ++line;
            col=1;
        }
    }
	pos pe=cod[cod.size()-1].p;
    ++pe.column;
    posc poe;
    poe.p=pe;
    poe.c='\0';
    cod.push_back(poe);
	return cod;
}
// get DFA from regular expression
vector<DFAnode> getDFA(string re){
	string rep = ShuntingYard(re);
	//cout << rep << endl;
	NFA.clear();
	DFA.clear();
	D.clear();
	subNFA nfa=Thompson(rep);
	//printnfa(nfa);
	chars=getchars(rep);
	subsetConstruction(nfa.start,nfa);
	return DFA;
}
/*int main() {
	string re,rep;
	cin >> re;
	rep = ShuntingYard(re);
	//cout << rep << endl;
	subNFA nfa=Thompson(rep);
	chars=getchars(rep);
	/*for(auto it=chars.begin();it!=chars.end();++it){
		printf("%c",*it);
	}printf("\n");
	printf("%d\n",chars.size());*/
	//printnfa(nfa);
	/*subsetConstruction(nfa.start,nfa);
	printDFA();
	char fn[]={"aplusb.c"};
	vector<posc> cod=getcode(fn);
	for(int i=0;i<cod.size();++i){

	}*/

	// test closure and move
	/*set<int> clo0=closures(nfa.start);
	printf("clo0:\n");
	printset(clo0);
	set<int> moveaa=moveTa(clo0,'a');
	printf("moveaa:\n");
	printset(moveaa);
	set<int> B=closureT(moveaa);
	printf("B:\n");
	printset(B);
	printf("moveab:\n");
	set<int> moveab=moveTa(clo0,'b');
	printset(moveab);
	printf("C:\n");
	set<int> C=closureT(moveab);
	printset(C);*/
    /*system("pause");
	return 0;
} */
#endif