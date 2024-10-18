#define SOUFFLE_GENERATOR_VERSION "2.4.1-51-g437f28055"
#include "souffle/CompiledSouffle.h"
#include "souffle/SignalHandler.h"
#include "souffle/SouffleInterface.h"
#include "souffle/datastructure/BTree.h"
#include "souffle/io/IOSystem.h"
#include "souffle/utility/MiscUtil.h"
#include <any>
namespace functors {
extern "C" {
}
} //namespace functors
namespace souffle::t_btree_000_ii__0_1__11__10 {
using namespace souffle;
struct Type {
static constexpr Relation::arity_type Arity = 2;
using t_tuple = Tuple<RamDomain, 2>;
struct t_comparator_0{
 int operator()(const t_tuple& a, const t_tuple& b) const {
  return (ramBitCast<RamSigned>(a[0]) < ramBitCast<RamSigned>(b[0])) ? -1 : (ramBitCast<RamSigned>(a[0]) > ramBitCast<RamSigned>(b[0])) ? 1 :((ramBitCast<RamSigned>(a[1]) < ramBitCast<RamSigned>(b[1])) ? -1 : (ramBitCast<RamSigned>(a[1]) > ramBitCast<RamSigned>(b[1])) ? 1 :(0));
 }
bool less(const t_tuple& a, const t_tuple& b) const {
  return (ramBitCast<RamSigned>(a[0]) < ramBitCast<RamSigned>(b[0]))|| ((ramBitCast<RamSigned>(a[0]) == ramBitCast<RamSigned>(b[0])) && ((ramBitCast<RamSigned>(a[1]) < ramBitCast<RamSigned>(b[1]))));
 }
bool equal(const t_tuple& a, const t_tuple& b) const {
return (ramBitCast<RamSigned>(a[0]) == ramBitCast<RamSigned>(b[0]))&&(ramBitCast<RamSigned>(a[1]) == ramBitCast<RamSigned>(b[1]));
 }
};
using t_ind_0 = btree_set<t_tuple,t_comparator_0>;
t_ind_0 ind_0;
using iterator = t_ind_0::iterator;
struct context {
t_ind_0::operation_hints hints_0_lower;
t_ind_0::operation_hints hints_0_upper;
};
context createContext() { return context(); }
bool insert(const t_tuple& t);
bool insert(const t_tuple& t, context& h);
bool insert(const RamDomain* ramDomain);
bool insert(RamDomain a0,RamDomain a1);
bool contains(const t_tuple& t, context& h) const;
bool contains(const t_tuple& t) const;
std::size_t size() const;
iterator find(const t_tuple& t, context& h) const;
iterator find(const t_tuple& t) const;
range<iterator> lowerUpperRange_00(const t_tuple& /* lower */, const t_tuple& /* upper */, context& /* h */) const;
range<iterator> lowerUpperRange_00(const t_tuple& /* lower */, const t_tuple& /* upper */) const;
range<t_ind_0::iterator> lowerUpperRange_11(const t_tuple& lower, const t_tuple& upper, context& h) const;
range<t_ind_0::iterator> lowerUpperRange_11(const t_tuple& lower, const t_tuple& upper) const;
range<t_ind_0::iterator> lowerUpperRange_10(const t_tuple& lower, const t_tuple& upper, context& h) const;
range<t_ind_0::iterator> lowerUpperRange_10(const t_tuple& lower, const t_tuple& upper) const;
bool empty() const;
std::vector<range<iterator>> partition() const;
void purge();
iterator begin() const;
iterator end() const;
void printStatistics(std::ostream& o) const;
};
} // namespace souffle::t_btree_000_ii__0_1__11__10 
namespace souffle::t_btree_000_ii__0_1__11__10 {
using namespace souffle;
using t_ind_0 = Type::t_ind_0;
using iterator = Type::iterator;
using context = Type::context;
bool Type::insert(const t_tuple& t) {
context h;
return insert(t, h);
}
bool Type::insert(const t_tuple& t, context& h) {
if (ind_0.insert(t, h.hints_0_lower)) {
return true;
} else return false;
}
bool Type::insert(const RamDomain* ramDomain) {
RamDomain data[2];
std::copy(ramDomain, ramDomain + 2, data);
const t_tuple& tuple = reinterpret_cast<const t_tuple&>(data);
context h;
return insert(tuple, h);
}
bool Type::insert(RamDomain a0,RamDomain a1) {
RamDomain data[2] = {a0,a1};
return insert(data);
}
bool Type::contains(const t_tuple& t, context& h) const {
return ind_0.contains(t, h.hints_0_lower);
}
bool Type::contains(const t_tuple& t) const {
context h;
return contains(t, h);
}
std::size_t Type::size() const {
return ind_0.size();
}
iterator Type::find(const t_tuple& t, context& h) const {
return ind_0.find(t, h.hints_0_lower);
}
iterator Type::find(const t_tuple& t) const {
context h;
return find(t, h);
}
range<iterator> Type::lowerUpperRange_00(const t_tuple& /* lower */, const t_tuple& /* upper */, context& /* h */) const {
return range<iterator>(ind_0.begin(),ind_0.end());
}
range<iterator> Type::lowerUpperRange_00(const t_tuple& /* lower */, const t_tuple& /* upper */) const {
return range<iterator>(ind_0.begin(),ind_0.end());
}
range<t_ind_0::iterator> Type::lowerUpperRange_11(const t_tuple& lower, const t_tuple& upper, context& h) const {
t_comparator_0 comparator;
int cmp = comparator(lower, upper);
if (cmp == 0) {
    auto pos = ind_0.find(lower, h.hints_0_lower);
    auto fin = ind_0.end();
    if (pos != fin) {fin = pos; ++fin;}
    return make_range(pos, fin);
}
if (cmp > 0) {
    return make_range(ind_0.end(), ind_0.end());
}
return make_range(ind_0.lower_bound(lower, h.hints_0_lower), ind_0.upper_bound(upper, h.hints_0_upper));
}
range<t_ind_0::iterator> Type::lowerUpperRange_11(const t_tuple& lower, const t_tuple& upper) const {
context h;
return lowerUpperRange_11(lower,upper,h);
}
range<t_ind_0::iterator> Type::lowerUpperRange_10(const t_tuple& lower, const t_tuple& upper, context& h) const {
t_comparator_0 comparator;
int cmp = comparator(lower, upper);
if (cmp > 0) {
    return make_range(ind_0.end(), ind_0.end());
}
return make_range(ind_0.lower_bound(lower, h.hints_0_lower), ind_0.upper_bound(upper, h.hints_0_upper));
}
range<t_ind_0::iterator> Type::lowerUpperRange_10(const t_tuple& lower, const t_tuple& upper) const {
context h;
return lowerUpperRange_10(lower,upper,h);
}
bool Type::empty() const {
return ind_0.empty();
}
std::vector<range<iterator>> Type::partition() const {
return ind_0.getChunks(400);
}
void Type::purge() {
ind_0.clear();
}
iterator Type::begin() const {
return ind_0.begin();
}
iterator Type::end() const {
return ind_0.end();
}
void Type::printStatistics(std::ostream& o) const {
o << " arity 2 direct b-tree index 0 lex-order [0,1]\n";
ind_0.printStats(o);
}
} // namespace souffle::t_btree_000_ii__0_1__11__10 
namespace souffle::t_btree_000_ii__0_1__11 {
using namespace souffle;
struct Type {
static constexpr Relation::arity_type Arity = 2;
using t_tuple = Tuple<RamDomain, 2>;
struct t_comparator_0{
 int operator()(const t_tuple& a, const t_tuple& b) const {
  return (ramBitCast<RamSigned>(a[0]) < ramBitCast<RamSigned>(b[0])) ? -1 : (ramBitCast<RamSigned>(a[0]) > ramBitCast<RamSigned>(b[0])) ? 1 :((ramBitCast<RamSigned>(a[1]) < ramBitCast<RamSigned>(b[1])) ? -1 : (ramBitCast<RamSigned>(a[1]) > ramBitCast<RamSigned>(b[1])) ? 1 :(0));
 }
bool less(const t_tuple& a, const t_tuple& b) const {
  return (ramBitCast<RamSigned>(a[0]) < ramBitCast<RamSigned>(b[0]))|| ((ramBitCast<RamSigned>(a[0]) == ramBitCast<RamSigned>(b[0])) && ((ramBitCast<RamSigned>(a[1]) < ramBitCast<RamSigned>(b[1]))));
 }
bool equal(const t_tuple& a, const t_tuple& b) const {
return (ramBitCast<RamSigned>(a[0]) == ramBitCast<RamSigned>(b[0]))&&(ramBitCast<RamSigned>(a[1]) == ramBitCast<RamSigned>(b[1]));
 }
};
using t_ind_0 = btree_set<t_tuple,t_comparator_0>;
t_ind_0 ind_0;
using iterator = t_ind_0::iterator;
struct context {
t_ind_0::operation_hints hints_0_lower;
t_ind_0::operation_hints hints_0_upper;
};
context createContext() { return context(); }
bool insert(const t_tuple& t);
bool insert(const t_tuple& t, context& h);
bool insert(const RamDomain* ramDomain);
bool insert(RamDomain a0,RamDomain a1);
bool contains(const t_tuple& t, context& h) const;
bool contains(const t_tuple& t) const;
std::size_t size() const;
iterator find(const t_tuple& t, context& h) const;
iterator find(const t_tuple& t) const;
range<iterator> lowerUpperRange_00(const t_tuple& /* lower */, const t_tuple& /* upper */, context& /* h */) const;
range<iterator> lowerUpperRange_00(const t_tuple& /* lower */, const t_tuple& /* upper */) const;
range<t_ind_0::iterator> lowerUpperRange_11(const t_tuple& lower, const t_tuple& upper, context& h) const;
range<t_ind_0::iterator> lowerUpperRange_11(const t_tuple& lower, const t_tuple& upper) const;
bool empty() const;
std::vector<range<iterator>> partition() const;
void purge();
iterator begin() const;
iterator end() const;
void printStatistics(std::ostream& o) const;
};
} // namespace souffle::t_btree_000_ii__0_1__11 
namespace souffle::t_btree_000_ii__0_1__11 {
using namespace souffle;
using t_ind_0 = Type::t_ind_0;
using iterator = Type::iterator;
using context = Type::context;
bool Type::insert(const t_tuple& t) {
context h;
return insert(t, h);
}
bool Type::insert(const t_tuple& t, context& h) {
if (ind_0.insert(t, h.hints_0_lower)) {
return true;
} else return false;
}
bool Type::insert(const RamDomain* ramDomain) {
RamDomain data[2];
std::copy(ramDomain, ramDomain + 2, data);
const t_tuple& tuple = reinterpret_cast<const t_tuple&>(data);
context h;
return insert(tuple, h);
}
bool Type::insert(RamDomain a0,RamDomain a1) {
RamDomain data[2] = {a0,a1};
return insert(data);
}
bool Type::contains(const t_tuple& t, context& h) const {
return ind_0.contains(t, h.hints_0_lower);
}
bool Type::contains(const t_tuple& t) const {
context h;
return contains(t, h);
}
std::size_t Type::size() const {
return ind_0.size();
}
iterator Type::find(const t_tuple& t, context& h) const {
return ind_0.find(t, h.hints_0_lower);
}
iterator Type::find(const t_tuple& t) const {
context h;
return find(t, h);
}
range<iterator> Type::lowerUpperRange_00(const t_tuple& /* lower */, const t_tuple& /* upper */, context& /* h */) const {
return range<iterator>(ind_0.begin(),ind_0.end());
}
range<iterator> Type::lowerUpperRange_00(const t_tuple& /* lower */, const t_tuple& /* upper */) const {
return range<iterator>(ind_0.begin(),ind_0.end());
}
range<t_ind_0::iterator> Type::lowerUpperRange_11(const t_tuple& lower, const t_tuple& upper, context& h) const {
t_comparator_0 comparator;
int cmp = comparator(lower, upper);
if (cmp == 0) {
    auto pos = ind_0.find(lower, h.hints_0_lower);
    auto fin = ind_0.end();
    if (pos != fin) {fin = pos; ++fin;}
    return make_range(pos, fin);
}
if (cmp > 0) {
    return make_range(ind_0.end(), ind_0.end());
}
return make_range(ind_0.lower_bound(lower, h.hints_0_lower), ind_0.upper_bound(upper, h.hints_0_upper));
}
range<t_ind_0::iterator> Type::lowerUpperRange_11(const t_tuple& lower, const t_tuple& upper) const {
context h;
return lowerUpperRange_11(lower,upper,h);
}
bool Type::empty() const {
return ind_0.empty();
}
std::vector<range<iterator>> Type::partition() const {
return ind_0.getChunks(400);
}
void Type::purge() {
ind_0.clear();
}
iterator Type::begin() const {
return ind_0.begin();
}
iterator Type::end() const {
return ind_0.end();
}
void Type::printStatistics(std::ostream& o) const {
o << " arity 2 direct b-tree index 0 lex-order [0,1]\n";
ind_0.printStats(o);
}
} // namespace souffle::t_btree_000_ii__0_1__11 
namespace  souffle {
using namespace souffle;
class Stratum_edge_b821c9a100eb5b8d {
public:
 Stratum_edge_b821c9a100eb5b8d(SymbolTable& symTable,RecordTable& recordTable,ConcurrentCache<std::string,std::regex>& regexCache,bool& pruneImdtRels,bool& performIO,SignalHandler*& signalHandler,std::atomic<std::size_t>& iter,std::atomic<RamDomain>& ctr,std::string& inputDirectory,std::string& outputDirectory,t_btree_000_ii__0_1__11__10::Type& rel_edge_f2967ee81645a356);
void run([[maybe_unused]] const std::vector<RamDomain>& args,[[maybe_unused]] std::vector<RamDomain>& ret);
private:
SymbolTable& symTable;
RecordTable& recordTable;
ConcurrentCache<std::string,std::regex>& regexCache;
bool& pruneImdtRels;
bool& performIO;
SignalHandler*& signalHandler;
std::atomic<std::size_t>& iter;
std::atomic<RamDomain>& ctr;
std::string& inputDirectory;
std::string& outputDirectory;
t_btree_000_ii__0_1__11__10::Type* rel_edge_f2967ee81645a356;
};
} // namespace  souffle
namespace  souffle {
using namespace souffle;
 Stratum_edge_b821c9a100eb5b8d::Stratum_edge_b821c9a100eb5b8d(SymbolTable& symTable,RecordTable& recordTable,ConcurrentCache<std::string,std::regex>& regexCache,bool& pruneImdtRels,bool& performIO,SignalHandler*& signalHandler,std::atomic<std::size_t>& iter,std::atomic<RamDomain>& ctr,std::string& inputDirectory,std::string& outputDirectory,t_btree_000_ii__0_1__11__10::Type& rel_edge_f2967ee81645a356):
symTable(symTable),
recordTable(recordTable),
regexCache(regexCache),
pruneImdtRels(pruneImdtRels),
performIO(performIO),
signalHandler(signalHandler),
iter(iter),
ctr(ctr),
inputDirectory(inputDirectory),
outputDirectory(outputDirectory),
rel_edge_f2967ee81645a356(&rel_edge_f2967ee81645a356){
}

void Stratum_edge_b821c9a100eb5b8d::run([[maybe_unused]] const std::vector<RamDomain>& args,[[maybe_unused]] std::vector<RamDomain>& ret){
if (performIO) {
try {std::map<std::string, std::string> directiveMap({{"IO","file"},{"attributeNames","x\ty"},{"auxArity","0"},{"fact-dir","."},{"name","edge"},{"operation","input"},{"params","{\"records\": {}, \"relation\": {\"arity\": 2, \"params\": [\"x\", \"y\"]}}"},{"types","{\"ADTs\": {}, \"records\": {}, \"relation\": {\"arity\": 2, \"types\": [\"i:number\", \"i:number\"]}}"}});
if (!inputDirectory.empty()) {directiveMap["fact-dir"] = inputDirectory;}
IOSystem::getInstance().getReader(directiveMap, symTable, recordTable)->readAll(*rel_edge_f2967ee81645a356);
} catch (std::exception& e) {std::cerr << "Error loading edge data: " << e.what() << '\n';
exit(1);
}
}
}

} // namespace  souffle

namespace  souffle {
using namespace souffle;
class Stratum_path_04e315f6f499c9d3 {
public:
 Stratum_path_04e315f6f499c9d3(SymbolTable& symTable,RecordTable& recordTable,ConcurrentCache<std::string,std::regex>& regexCache,bool& pruneImdtRels,bool& performIO,SignalHandler*& signalHandler,std::atomic<std::size_t>& iter,std::atomic<RamDomain>& ctr,std::string& inputDirectory,std::string& outputDirectory,t_btree_000_ii__0_1__11::Type& rel_delta_path_325b33c724e55970,t_btree_000_ii__0_1__11::Type& rel_new_path_f62f3c3704df2e4a,t_btree_000_ii__0_1__11__10::Type& rel_edge_f2967ee81645a356,t_btree_000_ii__0_1__11::Type& rel_path_2405b3b40fb3c138);
void run([[maybe_unused]] const std::vector<RamDomain>& args,[[maybe_unused]] std::vector<RamDomain>& ret);
private:
SymbolTable& symTable;
RecordTable& recordTable;
ConcurrentCache<std::string,std::regex>& regexCache;
bool& pruneImdtRels;
bool& performIO;
SignalHandler*& signalHandler;
std::atomic<std::size_t>& iter;
std::atomic<RamDomain>& ctr;
std::string& inputDirectory;
std::string& outputDirectory;
t_btree_000_ii__0_1__11::Type* rel_delta_path_325b33c724e55970;
t_btree_000_ii__0_1__11::Type* rel_new_path_f62f3c3704df2e4a;
t_btree_000_ii__0_1__11__10::Type* rel_edge_f2967ee81645a356;
t_btree_000_ii__0_1__11::Type* rel_path_2405b3b40fb3c138;
};
} // namespace  souffle
namespace  souffle {
using namespace souffle;
 Stratum_path_04e315f6f499c9d3::Stratum_path_04e315f6f499c9d3(SymbolTable& symTable,RecordTable& recordTable,ConcurrentCache<std::string,std::regex>& regexCache,bool& pruneImdtRels,bool& performIO,SignalHandler*& signalHandler,std::atomic<std::size_t>& iter,std::atomic<RamDomain>& ctr,std::string& inputDirectory,std::string& outputDirectory,t_btree_000_ii__0_1__11::Type& rel_delta_path_325b33c724e55970,t_btree_000_ii__0_1__11::Type& rel_new_path_f62f3c3704df2e4a,t_btree_000_ii__0_1__11__10::Type& rel_edge_f2967ee81645a356,t_btree_000_ii__0_1__11::Type& rel_path_2405b3b40fb3c138):
symTable(symTable),
recordTable(recordTable),
regexCache(regexCache),
pruneImdtRels(pruneImdtRels),
performIO(performIO),
signalHandler(signalHandler),
iter(iter),
ctr(ctr),
inputDirectory(inputDirectory),
outputDirectory(outputDirectory),
rel_delta_path_325b33c724e55970(&rel_delta_path_325b33c724e55970),
rel_new_path_f62f3c3704df2e4a(&rel_new_path_f62f3c3704df2e4a),
rel_edge_f2967ee81645a356(&rel_edge_f2967ee81645a356),
rel_path_2405b3b40fb3c138(&rel_path_2405b3b40fb3c138){
}

void Stratum_path_04e315f6f499c9d3::run([[maybe_unused]] const std::vector<RamDomain>& args,[[maybe_unused]] std::vector<RamDomain>& ret){
signalHandler->setMsg(R"_(path(x,y) :- 
   edge(x,y).
in file test.dl [7:1-7:26])_");
if(!(rel_edge_f2967ee81645a356->empty())) {
[&](){
CREATE_OP_CONTEXT(rel_edge_f2967ee81645a356_op_ctxt,rel_edge_f2967ee81645a356->createContext());
CREATE_OP_CONTEXT(rel_path_2405b3b40fb3c138_op_ctxt,rel_path_2405b3b40fb3c138->createContext());
for(const auto& env0 : *rel_edge_f2967ee81645a356) {
Tuple<RamDomain,2> tuple{{ramBitCast(env0[0]),ramBitCast(env0[1])}};
rel_path_2405b3b40fb3c138->insert(tuple,READ_OP_CONTEXT(rel_path_2405b3b40fb3c138_op_ctxt));
}
}
();}
[&](){
CREATE_OP_CONTEXT(rel_delta_path_325b33c724e55970_op_ctxt,rel_delta_path_325b33c724e55970->createContext());
CREATE_OP_CONTEXT(rel_path_2405b3b40fb3c138_op_ctxt,rel_path_2405b3b40fb3c138->createContext());
for(const auto& env0 : *rel_path_2405b3b40fb3c138) {
Tuple<RamDomain,2> tuple{{ramBitCast(env0[0]),ramBitCast(env0[1])}};
rel_delta_path_325b33c724e55970->insert(tuple,READ_OP_CONTEXT(rel_delta_path_325b33c724e55970_op_ctxt));
}
}
();auto loop_counter = RamUnsigned(1);
iter = 0;
for(;;) {
signalHandler->setMsg(R"_(path(x,y) :- 
   path(x,z),
   edge(z,y).
in file test.dl [8:1-8:38])_");
if(!(rel_delta_path_325b33c724e55970->empty()) && !(rel_edge_f2967ee81645a356->empty())) {
[&](){
CREATE_OP_CONTEXT(rel_delta_path_325b33c724e55970_op_ctxt,rel_delta_path_325b33c724e55970->createContext());
CREATE_OP_CONTEXT(rel_new_path_f62f3c3704df2e4a_op_ctxt,rel_new_path_f62f3c3704df2e4a->createContext());
CREATE_OP_CONTEXT(rel_edge_f2967ee81645a356_op_ctxt,rel_edge_f2967ee81645a356->createContext());
CREATE_OP_CONTEXT(rel_path_2405b3b40fb3c138_op_ctxt,rel_path_2405b3b40fb3c138->createContext());
for(const auto& env0 : *rel_delta_path_325b33c724e55970) {
auto range = rel_edge_f2967ee81645a356->lowerUpperRange_10(Tuple<RamDomain,2>{{ramBitCast(env0[1]), ramBitCast<RamDomain>(MIN_RAM_SIGNED)}},Tuple<RamDomain,2>{{ramBitCast(env0[1]), ramBitCast<RamDomain>(MAX_RAM_SIGNED)}},READ_OP_CONTEXT(rel_edge_f2967ee81645a356_op_ctxt));
for(const auto& env1 : range) {
if( !(rel_path_2405b3b40fb3c138->contains(Tuple<RamDomain,2>{{ramBitCast(env0[0]),ramBitCast(env1[1])}},READ_OP_CONTEXT(rel_path_2405b3b40fb3c138_op_ctxt)))) {
Tuple<RamDomain,2> tuple{{ramBitCast(env0[0]),ramBitCast(env1[1])}};
rel_new_path_f62f3c3704df2e4a->insert(tuple,READ_OP_CONTEXT(rel_new_path_f62f3c3704df2e4a_op_ctxt));
}
}
}
}
();}
if(rel_new_path_f62f3c3704df2e4a->empty()) break;
[&](){
CREATE_OP_CONTEXT(rel_new_path_f62f3c3704df2e4a_op_ctxt,rel_new_path_f62f3c3704df2e4a->createContext());
CREATE_OP_CONTEXT(rel_path_2405b3b40fb3c138_op_ctxt,rel_path_2405b3b40fb3c138->createContext());
for(const auto& env0 : *rel_new_path_f62f3c3704df2e4a) {
Tuple<RamDomain,2> tuple{{ramBitCast(env0[0]),ramBitCast(env0[1])}};
rel_path_2405b3b40fb3c138->insert(tuple,READ_OP_CONTEXT(rel_path_2405b3b40fb3c138_op_ctxt));
}
}
();std::swap(rel_delta_path_325b33c724e55970, rel_new_path_f62f3c3704df2e4a);
rel_new_path_f62f3c3704df2e4a->purge();
loop_counter = (ramBitCast<RamUnsigned>(loop_counter) + ramBitCast<RamUnsigned>(RamUnsigned(1)));
iter++;
}
iter = 0;
rel_delta_path_325b33c724e55970->purge();
rel_new_path_f62f3c3704df2e4a->purge();
if (performIO) {
try {std::map<std::string, std::string> directiveMap({{"IO","file"},{"attributeNames","x\ty"},{"auxArity","0"},{"name","path"},{"operation","output"},{"output-dir","."},{"params","{\"records\": {}, \"relation\": {\"arity\": 2, \"params\": [\"x\", \"y\"]}}"},{"types","{\"ADTs\": {}, \"records\": {}, \"relation\": {\"arity\": 2, \"types\": [\"i:number\", \"i:number\"]}}"}});
if (outputDirectory == "-"){directiveMap["IO"] = "stdout"; directiveMap["headers"] = "true";}
else if (!outputDirectory.empty()) {directiveMap["output-dir"] = outputDirectory;}
IOSystem::getInstance().getWriter(directiveMap, symTable, recordTable)->writeAll(*rel_path_2405b3b40fb3c138);
} catch (std::exception& e) {std::cerr << e.what();exit(1);}
}
if (pruneImdtRels) rel_edge_f2967ee81645a356->purge();
}

} // namespace  souffle

namespace  souffle {
using namespace souffle;
class Sf_example: public SouffleProgram {
public:
 Sf_example();
 ~Sf_example();
void run();
void runAll(std::string inputDirectoryArg = "",std::string outputDirectoryArg = "",bool performIOArg = true,bool pruneImdtRelsArg = true);
void printAll([[maybe_unused]] std::string outputDirectoryArg = "");
void loadAll([[maybe_unused]] std::string inputDirectoryArg = "");
void dumpInputs();
void dumpOutputs();
SymbolTable& getSymbolTable();
RecordTable& getRecordTable();
void setNumThreads(std::size_t numThreadsValue);
void executeSubroutine(std::string name,const std::vector<RamDomain>& args,std::vector<RamDomain>& ret);
private:
void runFunction(std::string inputDirectoryArg,std::string outputDirectoryArg,bool performIOArg,bool pruneImdtRelsArg);
SymbolTableImpl symTable;
SpecializedRecordTable<0> recordTable;
ConcurrentCache<std::string,std::regex> regexCache;
Own<t_btree_000_ii__0_1__11__10::Type> rel_edge_f2967ee81645a356;
souffle::RelationWrapper<t_btree_000_ii__0_1__11__10::Type> wrapper_rel_edge_f2967ee81645a356;
Own<t_btree_000_ii__0_1__11::Type> rel_path_2405b3b40fb3c138;
souffle::RelationWrapper<t_btree_000_ii__0_1__11::Type> wrapper_rel_path_2405b3b40fb3c138;
Own<t_btree_000_ii__0_1__11::Type> rel_new_path_f62f3c3704df2e4a;
Own<t_btree_000_ii__0_1__11::Type> rel_delta_path_325b33c724e55970;
Stratum_edge_b821c9a100eb5b8d stratum_edge_bd08e9a8f799e828;
Stratum_path_04e315f6f499c9d3 stratum_path_32ce85b2a32d6a1b;
std::string inputDirectory;
std::string outputDirectory;
SignalHandler* signalHandler{SignalHandler::instance()};
std::atomic<RamDomain> ctr{};
std::atomic<std::size_t> iter{};
};
} // namespace  souffle
namespace  souffle {
using namespace souffle;
 Sf_example::Sf_example():
symTable(),
recordTable(),
regexCache(),
rel_edge_f2967ee81645a356(mk<t_btree_000_ii__0_1__11__10::Type>()),
wrapper_rel_edge_f2967ee81645a356(0, *rel_edge_f2967ee81645a356, *this, "edge", std::array<const char *,2>{{"i:number","i:number"}}, std::array<const char *,2>{{"x","y"}}, 0),
rel_path_2405b3b40fb3c138(mk<t_btree_000_ii__0_1__11::Type>()),
wrapper_rel_path_2405b3b40fb3c138(1, *rel_path_2405b3b40fb3c138, *this, "path", std::array<const char *,2>{{"i:number","i:number"}}, std::array<const char *,2>{{"x","y"}}, 0),
rel_new_path_f62f3c3704df2e4a(mk<t_btree_000_ii__0_1__11::Type>()),
rel_delta_path_325b33c724e55970(mk<t_btree_000_ii__0_1__11::Type>()),
stratum_edge_bd08e9a8f799e828(symTable,recordTable,regexCache,pruneImdtRels,performIO,signalHandler,iter,ctr,inputDirectory,outputDirectory,*rel_edge_f2967ee81645a356),
stratum_path_32ce85b2a32d6a1b(symTable,recordTable,regexCache,pruneImdtRels,performIO,signalHandler,iter,ctr,inputDirectory,outputDirectory,*rel_delta_path_325b33c724e55970,*rel_new_path_f62f3c3704df2e4a,*rel_edge_f2967ee81645a356,*rel_path_2405b3b40fb3c138){
addRelation("edge", wrapper_rel_edge_f2967ee81645a356, true, false);
addRelation("path", wrapper_rel_path_2405b3b40fb3c138, false, true);
}

 Sf_example::~Sf_example(){
}

void Sf_example::runFunction(std::string inputDirectoryArg,std::string outputDirectoryArg,bool performIOArg,bool pruneImdtRelsArg){

    this->inputDirectory  = std::move(inputDirectoryArg);
    this->outputDirectory = std::move(outputDirectoryArg);
    this->performIO       = performIOArg;
    this->pruneImdtRels   = pruneImdtRelsArg;

    // set default threads (in embedded mode)
    // if this is not set, and omp is used, the default omp setting of number of cores is used.
#if defined(_OPENMP)
    if (0 < getNumThreads()) { omp_set_num_threads(static_cast<int>(getNumThreads())); }
#endif

    signalHandler->set();
// -- query evaluation --
{
 std::vector<RamDomain> args, ret;
stratum_edge_bd08e9a8f799e828.run(args, ret);
}
{
 std::vector<RamDomain> args, ret;
stratum_path_32ce85b2a32d6a1b.run(args, ret);
}

// -- relation hint statistics --
signalHandler->reset();
}

void Sf_example::run(){
runFunction("", "", false, false);
}

void Sf_example::runAll(std::string inputDirectoryArg,std::string outputDirectoryArg,bool performIOArg,bool pruneImdtRelsArg){
runFunction(inputDirectoryArg, outputDirectoryArg, performIOArg, pruneImdtRelsArg);
}

void Sf_example::printAll([[maybe_unused]] std::string outputDirectoryArg){
try {std::map<std::string, std::string> directiveMap({{"IO","file"},{"attributeNames","x\ty"},{"auxArity","0"},{"name","path"},{"operation","output"},{"output-dir","."},{"params","{\"records\": {}, \"relation\": {\"arity\": 2, \"params\": [\"x\", \"y\"]}}"},{"types","{\"ADTs\": {}, \"records\": {}, \"relation\": {\"arity\": 2, \"types\": [\"i:number\", \"i:number\"]}}"}});
if (!outputDirectoryArg.empty()) {directiveMap["output-dir"] = outputDirectoryArg;}
IOSystem::getInstance().getWriter(directiveMap, symTable, recordTable)->writeAll(*rel_path_2405b3b40fb3c138);
} catch (std::exception& e) {std::cerr << e.what();exit(1);}
}

void Sf_example::loadAll([[maybe_unused]] std::string inputDirectoryArg){
try {std::map<std::string, std::string> directiveMap({{"IO","file"},{"attributeNames","x\ty"},{"auxArity","0"},{"fact-dir","."},{"name","edge"},{"operation","input"},{"params","{\"records\": {}, \"relation\": {\"arity\": 2, \"params\": [\"x\", \"y\"]}}"},{"types","{\"ADTs\": {}, \"records\": {}, \"relation\": {\"arity\": 2, \"types\": [\"i:number\", \"i:number\"]}}"}});
if (!inputDirectoryArg.empty()) {directiveMap["fact-dir"] = inputDirectoryArg;}
IOSystem::getInstance().getReader(directiveMap, symTable, recordTable)->readAll(*rel_edge_f2967ee81645a356);
} catch (std::exception& e) {std::cerr << "Error loading edge data: " << e.what() << '\n';
exit(1);
}
}

void Sf_example::dumpInputs(){
try {std::map<std::string, std::string> rwOperation;
rwOperation["IO"] = "stdout";
rwOperation["name"] = "edge";
rwOperation["types"] = "{\"relation\": {\"arity\": 2, \"auxArity\": 0, \"types\": [\"i:number\", \"i:number\"]}}";
IOSystem::getInstance().getWriter(rwOperation, symTable, recordTable)->writeAll(*rel_edge_f2967ee81645a356);
} catch (std::exception& e) {std::cerr << e.what();exit(1);}
}

void Sf_example::dumpOutputs(){
try {std::map<std::string, std::string> rwOperation;
rwOperation["IO"] = "stdout";
rwOperation["name"] = "path";
rwOperation["types"] = "{\"relation\": {\"arity\": 2, \"auxArity\": 0, \"types\": [\"i:number\", \"i:number\"]}}";
IOSystem::getInstance().getWriter(rwOperation, symTable, recordTable)->writeAll(*rel_path_2405b3b40fb3c138);
} catch (std::exception& e) {std::cerr << e.what();exit(1);}
}

SymbolTable& Sf_example::getSymbolTable(){
return symTable;
}

RecordTable& Sf_example::getRecordTable(){
return recordTable;
}

void Sf_example::setNumThreads(std::size_t numThreadsValue){
SouffleProgram::setNumThreads(numThreadsValue);
symTable.setNumLanes(getNumThreads());
recordTable.setNumLanes(getNumThreads());
regexCache.setNumLanes(getNumThreads());
}

void Sf_example::executeSubroutine(std::string name,const std::vector<RamDomain>& args,std::vector<RamDomain>& ret){
if (name == "edge") {
stratum_edge_bd08e9a8f799e828.run(args, ret);
return;}
if (name == "path") {
stratum_path_32ce85b2a32d6a1b.run(args, ret);
return;}
fatal(("unknown subroutine " + name).c_str());
}

} // namespace  souffle
namespace souffle {
SouffleProgram *newInstance_example(){return new  souffle::Sf_example;}
SymbolTable *getST_example(SouffleProgram *p){return &reinterpret_cast<souffle::Sf_example*>(p)->getSymbolTable();}
} // namespace souffle

#ifndef __EMBEDDED_SOUFFLE__
#include "souffle/CompiledOptions.h"
int main(int argc, char** argv)
{
try{
souffle::CmdOptions opt(R"(test.dl)",
R"()",
R"()",
false,
R"()",
1);
if (!opt.parse(argc,argv)) return 1;
souffle::Sf_example obj;
#if defined(_OPENMP) 
obj.setNumThreads(opt.getNumJobs());

#endif
obj.runAll(opt.getInputFileDir(), opt.getOutputFileDir());
return 0;
} catch(std::exception &e) { souffle::SignalHandler::instance()->error(e.what());}
}
#endif

namespace  souffle {
using namespace souffle;
class factory_Sf_example: souffle::ProgramFactory {
public:
souffle::SouffleProgram* newInstance();
 factory_Sf_example();
private:
};
} // namespace  souffle
namespace  souffle {
using namespace souffle;
souffle::SouffleProgram* factory_Sf_example::newInstance(){
return new  souffle::Sf_example();
}

 factory_Sf_example::factory_Sf_example():
souffle::ProgramFactory("example"){
}

} // namespace  souffle
namespace souffle {

#ifdef __EMBEDDED_SOUFFLE__
extern "C" {
souffle::factory_Sf_example __factory_Sf_example_instance;
}
#endif
} // namespace souffle

