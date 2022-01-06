#include<iostream>
#include<string>
#include<vector>
#include<fstream>
#include<unordered_map>
#include<queue>
#include<chrono>
#include<stack>
using namespace std;

vector<string> variable_names={"a","b","c","d","e","f","g","h","i","j","k","l","m","n","o","p","q","r","s","t","u","v","w","x","y","z"};



string CNF_form(string temp,int a){         //Convert given form to CNF
    temp[a]='|';
    temp.erase(temp.begin()+(a+1));

    for(int i=a;i>=0;i--){
        if(temp[i]=='&'){
            temp[i]='|';
            if(temp[i+2]!='~')
                temp.insert(i+2,"~");
            else
                temp.erase(temp.begin()+(i+2));
        }
    }
    if(temp[0]=='~'){
        temp.erase(temp.begin());
    }
    else{
        temp.insert(temp.begin(),'~');
    }
    return temp;
}


bool isvariable(string s){
    if(islower(s[0])){
        return true;
        
    }
    else{
        return false;
    }
}

struct Predicate{                           // Make string predicates into objects
    bool sign;
    string predi;
    vector<string> args;
    public:
    Predicate(string temp){
        int a=0;
        while(temp[a]!='('){
            a++;
        }
        if(temp[0]=='~'){
            predi=temp.substr(1,a-1);
            sign=0;
        }
        else{
            predi=temp.substr(0,a);
            sign=1;
        }
        a++;
        int i=a;
        while(i<temp.size()){
            if(temp[i]==','||temp[i]==')'){
                string t=temp.substr(a,i-a);
                args.push_back(t);
                a=i+1;
            }
            i++;
        }
    }
    Predicate(const Predicate& rhs){
        sign=rhs.sign;
        predi=rhs.predi;
        string temp;
        for(string s:rhs.args){
            temp=s;
            args.push_back(temp);
        }
    }

    bool operator ==(const Predicate& rhs) const{
        if(predi!=rhs.predi) return false;
        if(sign !=rhs.sign) return false;
        for(int i=0;i<args.size();i++){
            if(!isvariable(args[i]) && !isvariable(rhs.args[i]) && args[i]!=rhs.args[i]) return false;
        }
        return true;
    }
};



struct CNF_sent{                            //Make Sentences into vector of predicates
    vector<Predicate> sent;
    CNF_sent(string temp){
        int i=0,j=0;
        while(i<temp.size()){
            if(temp[i]=='|')
            {
                string t(temp,j,i-j);
                Predicate p1=Predicate(t);
                sent.push_back(p1);
                j=i+2;
                i++;
            }  
        i++;
        }
        string t2(temp,j,i-j);
        Predicate p2= Predicate(t2);
        sent.push_back(p2);
    }
    CNF_sent(const CNF_sent& rhs){
       for(Predicate p:rhs.sent){
           Predicate p1=p;
           sent.push_back(p1);
       }     
    }

    void negate(){
        for(Predicate &p1:sent){
            if(p1.sign==1) p1.sign=0;
            else p1.sign=1;
        }
    }
    void print(){
        for(Predicate& i: sent){
            cout<<i.sign<<" "<<i.predi<<" ";
            for(string j:i.args){
                cout<<j<<" ";        
            }
            cout<<endl;
        }
    }
};






class Knowledge_store{
    public:
    vector<CNF_sent> literals;
    vector<CNF_sent> sentences;
    unordered_map<string,vector<int>> literal_pos;                        //Store position of literals
    unordered_map<string,vector<pair<int,int>>> sentence_pos;             //Store position of sentences
    Knowledge_store() {
        literals=vector<CNF_sent>{};
        sentences=vector<CNF_sent>{};
        literal_pos=unordered_map<string,vector<int>>{};
        sentence_pos=unordered_map<string,vector<pair<int,int>>>{};

    }
    Knowledge_store(const Knowledge_store& rhs){
        literals=rhs.literals;
        sentences=rhs.sentences;
        literal_pos=rhs.literal_pos;
        sentence_pos=rhs.sentence_pos;
    }

    void insert(CNF_sent st){
        if(st.sent.size()==1){
            literals.push_back(st);
            if(literal_pos.find(st.sent[0].predi)==literal_pos.end()){
                literal_pos[st.sent[0].predi]= vector<int>{};
            }
            literal_pos[st.sent[0].predi].push_back(literals.size()-1);
        }
        else if(st.sent.size()>1){
            sentences.push_back(st);
            for(int i=0;i<st.sent.size();i++){
                if(sentence_pos.find(st.sent[i].predi)==sentence_pos.end()){
                    sentence_pos[st.sent[i].predi]= vector<pair<int,int>>{};
                }
                sentence_pos[st.sent[i].predi].push_back(make_pair(sentences.size()-1,i));
            }
        }
    }

};


struct Compare {
    bool operator()(CNF_sent const & a, CNF_sent const & b)
    { return a.sent.size() < b.sent.size(); }
};


bool literal_resolve(Knowledge_store &KB, stack<CNF_sent>& query_list, CNF_sent s2){
    priority_queue<CNF_sent,vector<CNF_sent>,Compare> priority_CNF;
    Predicate p1=s2.sent[0];
    if(KB.sentence_pos.find(p1.predi)!=KB.sentence_pos.end()){
        for(int k=0;k<KB.sentence_pos[p1.predi].size();k++){                            //Loop over all occureneces of the predicate in sentences
            int pos_sent=KB.sentence_pos[p1.predi][k].first;
            int pos_pred=KB.sentence_pos[p1.predi][k].second;
            CNF_sent s1=KB.sentences[pos_sent];                                         //Store sentence where the predicate appears
            Predicate p2= s1.sent[pos_pred];                                            //Store the predicate in sentence in a variable
            
            if(p1.sign!=p2.sign){                                                       //If signs are opposite they can be resolved
                int flag=0;
                for(int l=0;l<p1.args.size();l++){
                    // cout<<"Arguments"<<endl;
                    // cout<<p1.args[l]<<" "<<p2.args[l]<<endl;
                    if(!isvariable(p1.args[l]) && !isvariable(p2.args[l]) && p1.args[l]!=p2.args[l]){
                        flag=1;
                        break;
                    }
                }
                if(flag==0){
                    for(int l=0;l<p1.args.size();l++){
                        if(!isvariable(p1.args[l]) && isvariable(p2.args[l])){
                            string temp_var= p2.args[l];
                            string temp_const=p1.args[l];

                            for(Predicate &p_change:s1.sent){                          //Loop over the statement to find the varaible
                                for(string &arg_change:p_change.args){                 //Loop over argument to find the variable
                                    if(temp_var==arg_change){
                                    arg_change=temp_const;                             // Substitute the variable with the constant
                                    }
                                }
                            }
                        }
                    }
                
                    // cout<<"Changed Sentence"<<endl;
                    // s1.print();
                    s1.sent.erase(s1.sent.begin()+pos_pred);                                            //Erase the found predicate from sentence 
                    //cout<<"Resolved Sentence"<<endl;
                    //s1.print();
                    if(s1.sent.size()==1){
                        Predicate p3=s1.sent[0];                                                        //Make new literal

                        if(KB.literal_pos.find(p3.predi)!=KB.literal_pos.end()){                        //Check if the literal occured before 
                            for(int h=0;h<KB.literal_pos[p3.predi].size();h++){
                                Predicate p4=KB.literals[KB.literal_pos[p3.predi][h]].sent[0];          //Create p4 to compare with p3

                                if(p4.sign!=p3.sign){                                                   //Check if p3 and p4 are opposites
                                    int flag1=0;
                                    for(int g=0;g<p3.args.size();g++){

                                        if(!isvariable(p3.args[g]) && !isvariable(p4.args[g]) && p3.args[g]!=p4.args[g]){
                                            flag1=1;
                                            break;
                                        }
                                    }
                                    if(flag1==0){                                                       //If p3 and p4 are opposites, Contradiction found return true
                                        
                                        return true;
                                    }
                                }
                            }

                            KB.literals.push_back(s1);

                            KB.literal_pos[p3.predi].push_back(KB.literals.size()-1);                   //Insert S1 in the literals if no contradiction is found

                        }
                        else{                                                                           //If literal not already present
                             KB.literals.push_back(s1);

                             KB.literal_pos[p3.predi]=vector<int>{};                                     //Create key in hash table for new literal
                             KB.literal_pos[p3.predi].push_back(KB.literals.size()-1);                   //Insert position of new literal

                         }

                    }


                    else if(s1.sent.size()>1){                                                         // If size greater than 1 then add to KB sentences  

                        KB.sentences.push_back(s1);                                                    //Push sentence in KB
                        for(int c=0;c<s1.sent.size();c++){
                            if(KB.sentence_pos.find(s1.sent[c].predi)==KB.sentence_pos.end()){
                                KB.sentence_pos[s1.sent[c].predi]= vector<pair<int,int>>{};
                            }
                        KB.sentence_pos[s1.sent[c].predi].push_back(make_pair(KB.sentences.size()-1,c));
                        }

                    }
                    priority_CNF.push(s1);
                }
            }

        }

    }
    while(!priority_CNF.empty()){
        CNF_sent s25=priority_CNF.top();
        priority_CNF.pop();
        query_list.push(s25);
    }
    return false;

}

bool sentence_resolve(Knowledge_store& KB, stack<CNF_sent>& query_list, CNF_sent s1){
    priority_queue<CNF_sent,vector<CNF_sent>,Compare> priority_CNF;
    for(int ab=0;ab<s1.sent.size();ab++){
        Predicate p1=s1.sent[ab];
        CNF_sent s2=s1;
        if(KB.literal_pos.find(p1.predi)!=KB.literal_pos.end()){
            for(int i=0;i<KB.literal_pos[p1.predi].size();i++){
                Predicate p2=KB.literals[KB.literal_pos[p1.predi][i]].sent[0];
                if(p1.sign!=p2.sign){                                                       //If signs are opposite they can be resolved
                    int flag=0;
                    for(int l=0;l<p1.args.size();l++){
                        //cout<<"Arguments"<<endl;
                        //cout<<p1.args[l]<<" "<<p2.args[l]<<endl;
                        if(!isvariable(p1.args[l]) && !isvariable(p2.args[l]) && p1.args[l]!=p2.args[l]){
                            flag=1;
                            break;
                        }
                    }
                    if(flag==0){
                        for(int l=0;l<p1.args.size();l++){
                            if(!isvariable(p2.args[l]) && isvariable(p1.args[l])){
                                string temp_var= p1.args[l];
                                string temp_const=p2.args[l];

                                for(Predicate &p_change:s2.sent){                          //Loop over the statement to find the varaible
                                    for(string &arg_change:p_change.args){                 //Loop over argument to find the variable
                                        if(temp_var==arg_change){
                                        arg_change=temp_const;                             // Substitute the variable with the constant
                                        }
                                    }
                                }
                            }
                        }
                    
                        //cout<<"Changed Sentence"<<endl;
                        //s2.print();
                        s2.sent.erase(s2.sent.begin()+ab);                                            //Erase the found predicate from sentence 
                        //cout<<"Resolved Sentence"<<endl;
                        //s2.print();
                        if(s2.sent.size()==1){
                            Predicate p3=s2.sent[0];                                                        //Make new literal

                            if(KB.literal_pos.find(p3.predi)!=KB.literal_pos.end()){                        //Check if the literal occured before 
                                for(int h=0;h<KB.literal_pos[p3.predi].size();h++){
                                    Predicate p4=KB.literals[KB.literal_pos[p3.predi][h]].sent[0];          //Create p4 to compare with p3

                                    if(p4.sign!=p3.sign){                                                   //Check if p3 and p4 are opposites
                                        int flag1=0;
                                        for(int g=0;g<p3.args.size();g++){
                                            if(!isvariable(p3.args[g]) && !isvariable(p4.args[g]) && p3.args[g]!=p4.args[g]){
                                                flag1=1;

                                                break;
                                            }
                                        }
                                        if(flag1==0){                                                       //If p3 and p4 are opposites, Contradiction found return true
                                            
                                            return true;
                                        }
                                    }
                                }

                                KB.literals.push_back(s2);
                                KB.literal_pos[p3.predi].push_back(KB.literals.size()-1);                   //Insert S1 in the literals if no contradiction is found
    
                                
                            }
                            else{                                                                           //If literal not already present
                                KB.literals.push_back(s2);

                                KB.literal_pos[p3.predi]=vector<int>{};                                     //Create key in hash table for new literal
                                KB.literal_pos[p3.predi].push_back(KB.literals.size()-1);                   //Insert position of new literal


                            }

                        }


                        else if(s2.sent.size()>1){                                                         // If size greater than 1 then add to KB sentences  

                            KB.sentences.push_back(s2);                                                    //Push sentence in KB
                            for(int c=0;c<s2.sent.size();c++){
                                if(KB.sentence_pos.find(s2.sent[c].predi)==KB.sentence_pos.end()){
                                    KB.sentence_pos[s2.sent[c].predi]= vector<pair<int,int>>{};
                                }
                            KB.sentence_pos[s2.sent[c].predi].push_back(make_pair(KB.sentences.size()-1,c));
                            }

                        }
                        priority_CNF.push(s2);
                    }                         
                }
            }
        }   
        if(KB.sentence_pos.find(p1.predi)!=KB.sentence_pos.end()){
            for(int as=0;as<KB.sentence_pos[p1.predi].size();as++){
                int sentence_posi=KB.sentence_pos[p1.predi][as].first;
                int predi_position=KB.sentence_pos[p1.predi][as].second;
                CNF_sent s10=s1;
                CNF_sent s11=KB.sentences[sentence_posi];
                Predicate p10=s11.sent[predi_position];
                
                if(p1.sign!=p10.sign){
                    int flag10=0;
                    for(int kl=0;kl<p1.args.size();kl++){
                        if(!isvariable(p1.args[kl]) && !isvariable(p10.args[kl]) && p1.args[kl]!=p10.args[kl]){
                            flag10=1;
                            break;

                        }
                    }
                    if(flag10==0){

                        for(int sr=0;sr<p1.args.size();sr++){
                            if(isvariable(p1.args[sr]) && !isvariable(p10.args[sr])){
                                string variable_chang=p1.args[sr];
                                string constant_chang=p10.args[sr];
                                for(Predicate& p20:s10.sent){
                                    for(string& arg20:p20.args){
                                        if(arg20==variable_chang){
                                            arg20=constant_chang;
                                        }
                                    }
                                }

                            }
                            else if(isvariable(p10.args[sr]) && !isvariable(p1.args[sr])){
                                string varia_chang=p10.args[sr];
                                string const_chang=p1.args[sr];
                                for(Predicate& p30:s11.sent){
                                    for(string& arg30:p30.args){
                                        if(arg30==varia_chang){
                                            arg30=const_chang;
                                        }
                                    }
                                }

                            }


                        }
                        int flag_var=0;        
                        for(int ak=0;ak<p1.args.size();ak++){
                            if(isvariable(p1.args[ak]) || isvariable(p10.args[ak])){
                                flag_var=1;
                                break;
                            }
                        }
                        if(flag_var==1){
                            unordered_map<string,int>   left_sent;
                            unordered_map<string,int>  right_sent;
                            for(Predicate p40:s1.sent){
                                for(string arg40:p40.args){
                                    if(isvariable(arg40)){
                                        left_sent[arg40]=1;
                                    }
                                }
                            }
                            for(Predicate p50:s11.sent){
                                for(string arg50:p50.args){
                                    if(isvariable(arg50)){
                                        right_sent[arg50]=1;
                                    }
                                }
                            }
                            for(int pk=0;pk<p1.args.size();pk++){
                                if(isvariable(p1.args[pk]) && isvariable(p10.args[pk]))
                                {
                                    if(right_sent.find(p1.args[pk])==right_sent.end() || right_sent[p1.args[pk]]==0){
                                        for(Predicate &p60:s11.sent){
                                            for(string &arg60:p60.args){
                                                if(arg60==p10.args[pk]){
                                                    arg60=p1.args[pk];
                                                }
                                            }
                                        }
                                        right_sent[p1.args[pk]]=1;
                                    }     
                                    if(left_sent.find(p10.args[pk])==left_sent.end() || left_sent[p10.args[pk]]==0){
                                        for(Predicate &p70:s10.sent){
                                            for(string &arg70:p70.args){
                                                if(arg70==p1.args[pk]){
                                                    arg70=p10.args[pk];
                                                }
                                            }
                                        }
                                        left_sent[p10.args[pk]]=1;
                                    }
                                    else{
                                        string left_variable=p1.args[pk];
                                        string right_variable=p10.args[pk];
                                        left_sent[p1.args[pk]]=0;
                                        right_sent[p10.args[pk]]=0;
                                        string new_variable="";
                                        for(string var18:variable_names){
                                            if((left_sent.find(var18)==left_sent.end()||left_sent[var18]==0) && (right_sent.find(var18)==right_sent.end() || right_sent[var18]==0)){
                                                new_variable=var18;
                                                break;
                                            }
                                        }
                                        for(Predicate &p80:s10.sent){
                                            for(string &arg80:p80.args){
                                                if(arg80==left_variable){
                                                    arg80=new_variable;
                                                }
                                            }
                                        }
                                        for(Predicate &p90:s11.sent){
                                            for(string &arg90:p90.args){
                                                if(arg90==right_variable){
                                                    arg90=new_variable;
                                                }
                                            }
                                        }

                                    }


                                }   

                            }

                        }
                        s10.sent.erase(s10.sent.begin()+ab);
                        s11.sent.erase(s11.sent.begin()+predi_position);
                        s10.sent.insert(s10.sent.end(),s11.sent.begin(),s11.sent.end());
                        priority_CNF.push(s10);

                    
                    }
                }
            }
        }   
    }
    while(!priority_CNF.empty()){
        CNF_sent s35=priority_CNF.top();
        priority_CNF.pop();
        query_list.push(s35);
    }

    return false;
}


bool Resolver(Knowledge_store &KB, CNF_sent q){
    stack<CNF_sent> query_list;
    query_list.push(q);
    int i=1;
    auto start = chrono::high_resolution_clock::now(); 
    auto stop = chrono::high_resolution_clock::now();
    auto duration = chrono::duration_cast<chrono::microseconds>(stop - start);  
    while(!query_list.empty()){
        CNF_sent s1=query_list.top();
        //cout<<"Sentence "<<i++<<endl;
        //s1.print();
        query_list.pop();
        if(s1.sent.size()==1){
            if(literal_resolve(KB,query_list, s1)) return true;
        }
        else if(s1.sent.size()>1){
            if(sentence_resolve(KB,query_list, s1)) return true;
        }
        stop = chrono::high_resolution_clock::now();
        duration = chrono::duration_cast<chrono::microseconds>(stop - start);
        float time_elapsed=duration.count()/1000000.0;
        if(time_elapsed>100){
            cout<<time_elapsed<<endl;
            break;

        }
    }
    return false;

}





int main(){
    ifstream infile; 
    int q;                              
    infile.open("input.txt");
    vector<CNF_sent> queries;
    string temp_query="";
    infile>>q;
    getline(infile,temp_query);
    for(int i=0;i<q;i++){
        int a1 =0;
        getline(infile,temp_query);
        while(a1<temp_query.size()-1 && temp_query[a1]!='=' && temp_query[a1+1]!='>'){ a1++; }
        if(a1<temp_query.size()-1 && temp_query[a1]=='=' && temp_query[a1+1]=='>'){
            temp_query=CNF_form(temp_query,a1);
        }
        CNF_sent s1= CNF_sent(temp_query);
        queries.push_back(s1);
    }
    Knowledge_store KB;
    infile>>q;
    getline(infile,temp_query);

    for(int i=0;i<q;i++){
        getline(infile,temp_query);
        int a2 =0;
        while(a2<temp_query.size()-1 && temp_query[a2]!='=' && temp_query[a2+1]!='>'){ a2++;}
        if(a2<temp_query.size()-1 && temp_query[a2]=='=' && temp_query[a2+1]=='>'){
            temp_query=CNF_form(temp_query,a2);
        }
        CNF_sent s2=CNF_sent(temp_query);
        KB.insert(s2);
    }
    remove("output.txt");
    ofstream out;
    out.open("output.txt");
    int i=0;
    //cout<<queries.size();
    for(auto q1:queries){
        Knowledge_store new_KB=KB;
        q1.negate();
        

        if(Resolver(new_KB,q1)){
            out<<"TRUE";
            q1.negate();
            KB.insert(q1);
        }
        else{
            out<<"FALSE";
        }
        i++;
        if(i<queries.size()) out<<endl; 

    }    
    //cout<<endl<<endl<<endl;


    return 0;
}

