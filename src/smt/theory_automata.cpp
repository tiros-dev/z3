#include <array>
#include <map>
#include <queue>
#include <set>
#include <stack>
#include <typeinfo>
#include <vector>
#include "ast/ast.h"
#include "ast/ast_pp.h"
#include "smt/theory_automata.h"

namespace smt {

namespace automata {

unsigned alphabet_size = 256;

bool nfa::transition_less_than(const transition& a, const transition& b) {
    if (a._begin_char < b._begin_char) return true;
    if (a._begin_char == b._begin_char) {
        if (a._end_char < b._end_char) return true;
        if (a._end_char == b._end_char) {
            if (a._to_states < b._to_states) return true;
        }
    }
    return false;
}

bool nfa::transition_greater_than_obj::operator()(const transition& a, const transition& b) {
    return nfa::transition_less_than(b, a);
}

#ifdef Z3DEBUG
template<typename T, typename U = std::less_equal<T>>
static bool check_ordered(const std::vector<T>& v, U u = U()) {
    const T* prev = NULL;
    for (const T& i : v) {
        if (prev != NULL) {
            SASSERT(u(*prev, i));
        }
        prev = &i;
    }
    return true;
}
#endif // def Z3DEBUG

static std::vector<unsigned> merge_accending_vectors(const std::vector<unsigned>& as, const std::vector<unsigned>& bs) {
    SASSERT(check_ordered(as, std::less<unsigned>()));
    SASSERT(check_ordered(bs, std::less<unsigned>()));
    std::vector<unsigned> result;
    std::set_union(as.begin(), as.end(), bs.begin(), bs.end(), std::back_inserter(result));
    SASSERT(check_ordered(result, std::less<unsigned>()));
    return result;
}

static bool subset_of(const std::vector<unsigned>& as, const std::vector<unsigned>& bs) {
    SASSERT(check_ordered(as, std::less<unsigned>()));
    SASSERT(check_ordered(bs, std::less<unsigned>()));
    return std::includes(bs.begin(), bs.end(), as.begin(), as.end());
}

/*
 * Given a list of nfa transitions return the least equivalent list of nfa
 * transitions such that no two transitions overlap.
 *
 * TODO: pass the input as an iterator such that I can avoid copying
 * transitions into a temporary vector when normlizing a sequence of vectors of
 * transitions.
 */
static std::vector<nfa::transition> normalize_transitions(const std::vector<nfa::transition>& transitions) {
    if (transitions.empty()) {
        return std::vector<nfa::transition>();
    }
    std::priority_queue<nfa::transition, std::vector<nfa::transition>, nfa::transition_greater_than_obj> queue(transitions.begin(), transitions.end());
    std::vector<nfa::transition> result;
    nfa::transition* last = NULL;

    result.push_back(queue.top());
    queue.pop();
    last = &result[0];
#ifdef Z3DEBUG
    nfa::transition last_queue_pop = { std::vector<unsigned>(), 0, 0 }; // Technically not a valid transition
#endif // def Z3DEBUG
    while (!queue.empty()) {
        nfa::transition current = queue.top();
#ifdef Z3DEBUG
        SASSERT(nfa::transition_less_than(last_queue_pop, current)); // Ensure progress
        last_queue_pop = current;
#endif // def Z3DEBUG
        queue.pop();

        // Remove duplicate elements in the queue. This is techinically not needed, but it makes it easier to reason about progress
        while (!queue.empty() && queue.top() == current) {
            queue.pop();
        }

        // We are going to consider the last segment in result and the current segment
        // We want last and current to not overlap
        if (last->_begin_char == current._begin_char) {
            // The two segments starts with the same char
            if (last->_end_char == current._end_char) {
                // The two segments are equal. Merge to_states and discard current
                last->_to_states = merge_accending_vectors(last->_to_states, current._to_states);
            } else {
                SASSERT(last->_end_char < current._end_char); // *last < current in priority queue
                if (subset_of(last->_to_states, current._to_states)) {
                    // current subsumes *last, overwrite last
                    last->_end_char = current._end_char;
                    last->_to_states = current._to_states;
                } else {
                    last->_to_states = merge_accending_vectors(last->_to_states, current._to_states);
                    // *last covers current up to last->_end_char
                    current._begin_char = last->_end_char;
                    queue.push(current);
                }
            }
        } else {
            SASSERT(last->_begin_char < current._begin_char);
            if (last->_end_char < current._begin_char ||
                // No ordinary transition can subsume an epsilon transition
                (last->_begin_char < nfa::transition::epsilon_char && current._begin_char == nfa::transition::epsilon_char)) {
                // *last and current are disjoint and not kissing. Moving on.
                result.push_back(current);
                last = &result[result.size() - 1];
            } else {
                if (last->_to_states == current._to_states) {
                    // Merge(*last, current) subsumes both *last and current
                    last->_end_char = std::max(last->_end_char, current._end_char);
                } else {
                    std::vector<unsigned> merged_to_states = merge_accending_vectors(last->_to_states, current._to_states);
                    if (merged_to_states == last->_to_states) {
                        if (last->_end_char < current._end_char) {
                            // last subsumes a prefix of current
                            if (last->_end_char == current._begin_char) {
                                // The prefix of current was empty. Moving on
                                result.push_back(current);
                                last = &result[result.size() - 1];
                            } else {
                                // Discard prefix subsumed by *last
                                current._begin_char = last->_end_char;
                                queue.push(current);
                            }
                        } else {
                            // *last subsumes current. Discard current
                        }
                    } else if (merged_to_states == current._to_states) {
                        if (current._end_char < last->_end_char) {
                            // current subsumes a middle segment of *last
                            // Split *last and push the end of *last into queue
                            nfa::transition later = { last->_to_states, current._end_char, last->_end_char };
                            queue.push(later);
                        }
                        // current subsumes suffix of *last
                        last->_end_char = current._begin_char;
                        result.push_back(current);
                        last = &result[result.size() - 1];
                    } else {
                        SASSERT(current._begin_char <= last->_end_char);
                        // current and *last transition to different states
                        if (current._begin_char < last->_end_char) {
                            // Shorten *last and merge to_states on overlapping segment
                            unsigned last_end_char = last->_end_char;
                            last->_end_char = current._begin_char;
                            nfa::transition t = { merged_to_states, current._begin_char, std::min(last_end_char, current._end_char) };
                            if (last_end_char < current._end_char) {
                                // overlap(*last, current) does not cover all of current
                                // Add non-overlapping segment of current to queue
                                current._begin_char = last_end_char;
                                queue.push(current);
                            } else if (current._end_char < last_end_char) {
                                // *last has a suffix not covered by current. Push suffix to queue
                                queue.push({ last->_to_states, current._end_char, last_end_char });
                            }
                            result.push_back(t);
                            last = &result[result.size() - 1];
                        } else {
                            result.push_back(current);
                            last = &result[result.size() - 1];
                        }
                    }
                }
            }
        }
    }
#ifdef Z3DEBUG
    // Check that no segments overlap
    const nfa::transition* prev = NULL;
    for (const nfa::transition& current : result) {
        SASSERT(current.check_invariant());
        if (prev != NULL) {
            SASSERT(prev->_end_char <= current._begin_char);
            SASSERT(!prev->is_epsilon());
        }
        SASSERT(check_ordered(current._to_states, std::less<unsigned>()));
    }
#endif // def Z3DEBUG
    return result;
}

nfa::nfa(unsigned start_state,
         const std::set<unsigned>& accept_states,
         const transitions& transitions) :
    automaton<std::vector<unsigned>>(start_state, accept_states, normalize_transitions_map(transitions)) {
    SASSERT(check_invariant());
}

nfa::transitions nfa::normalize_transitions_map(const transitions& ts) {
    transitions result(ts.size());
    for (unsigned i = 0U; i < ts.size(); i++) {
        result[i] = normalize_transitions(ts[i]);
    }
    return result;
}

#ifdef Z3DEBUG
bool nfa::check_invariant() const {
    unsigned number_of_states = _transitions.size();
    SASSERT(_start_state < number_of_states);
    for (unsigned state = 0U; state < number_of_states; state++) {
        const std::vector<transition>& transitions = _transitions[state];
        const transition* previous_transition = NULL;
        for (const transition& transition : transitions) {
            SASSERT(check_ordered(transition._to_states, std::less<unsigned>()));
            for (unsigned s : transition._to_states) {
                SASSERT(s < number_of_states);
            }
            SASSERT(transition.check_invariant());
            if (previous_transition != NULL) {
                SASSERT(!previous_transition->is_epsilon());
                SASSERT(previous_transition->_end_char <= transition._begin_char);
            }
            previous_transition = &transition;
        }
    }
    for (unsigned state : _accept_states) {
        SASSERT(state < number_of_states);
    }
    return true;
}
#endif // def Z3DEBUG

nfa dfa::get_nfa() const {
    nfa::transitions nfa_transitions(_transitions.size());
    for (unsigned state = 0U; state < _transitions.size(); state++) {
        const std::vector<transition>& transitions = _transitions[state];
        std::vector<nfa::transition> new_transitions;
        for (const transition& t : transitions) {
            new_transitions.push_back({ std::vector<unsigned>(1, t._to_states.get_state()), t._begin_char, t._end_char });
        }
        nfa_transitions[state] = new_transitions;
    }
    return nfa(_start_state, _accept_states, nfa_transitions);
}

// Return the set of states reachable from the states in from_states via epsilon transitions
std::set<unsigned> nfa::epsilon_closure(const std::vector<unsigned>& from_states) const {
    std::set<unsigned> visited;
    std::stack<unsigned> future_work;

    for (unsigned state : from_states) {
        future_work.push(state);
    }

    while(!future_work.empty()) {
        unsigned state = future_work.top();
        future_work.pop();
        visited.insert(state);
        const std::vector<transition>& transitions = _transitions[state];
        if (!transitions.empty()) {
            const transition& t = transitions[transitions.size() - 1];
            if (t.is_epsilon()) {
                for (unsigned to_state : t._to_states) {
                    if (visited.count(to_state) == 0) {
                        future_work.push(to_state);
                    }
                }
            }
        }
    }
    return visited;
}

class dfa_builder {
private:
    unsigned _garbage_state;
    std::map<std::set<unsigned>, unsigned> _dfa_state_per_nfa_states;
    dfa::transitions _dfa_transitions;
    std::set<unsigned> _dfa_accept_states;
    const nfa& _nfa;

    unsigned garbage_state() {
        if (_garbage_state == std::numeric_limits<unsigned>::max()) {
            _garbage_state = next_dfa_state();
            _dfa_transitions[_garbage_state] = std::vector<dfa::transition>(1, { dfa_target(_garbage_state), 0, alphabet_size });
        }
        return _garbage_state;
    }

    unsigned next_dfa_state() {
        _dfa_transitions.push_back(std::vector<dfa::transition>());
        return _dfa_transitions.size() - 1;
    }

    unsigned get_dfa_state(const std::set<unsigned>& nfa_states) {
        auto it = _dfa_state_per_nfa_states.find(nfa_states);
        if (it == _dfa_state_per_nfa_states.end()) {
            unsigned s = next_dfa_state();
            _dfa_state_per_nfa_states[nfa_states] = s;
            for (unsigned nfa_state : nfa_states) {
                if (0 < _nfa._accept_states.count(nfa_state)) {
                    _dfa_accept_states.insert(s);
                }
            }
            return s;
        } else {
            return it->second;
        }
    }

public:
    dfa_builder(const nfa& n) : _garbage_state(std::numeric_limits<unsigned>::max()), _nfa(n) { };

    dfa get_dfa() {
        std::stack<std::set<unsigned>> nfa_state_sets_to_do;
        // set of dfa states where the coresponding nfa state set has been pushed onto nfa_state_sets_to_do
        std::set<unsigned> enqueued_dfa_states;

        nfa_state_sets_to_do.push(_nfa.epsilon_closure(std::vector<unsigned>(1, _nfa._start_state)));
        enqueued_dfa_states.insert(get_dfa_state(nfa_state_sets_to_do.top()));
        while (!nfa_state_sets_to_do.empty()) {
            std::set<unsigned> nfa_states = nfa_state_sets_to_do.top();
            nfa_state_sets_to_do.pop();
#ifdef Z3DEBUG
            std::vector<unsigned> nfa_states_vector(nfa_states.begin(), nfa_states.end());
            SASSERT(_nfa.epsilon_closure(nfa_states_vector) == nfa_states);
#endif // def Z3DEBUG
            unsigned dfa_state = get_dfa_state(nfa_states);
            std::vector<nfa::transition> epsilon_reachable_transitions;
            for (unsigned nfa_state : nfa_states) {
                epsilon_reachable_transitions.insert(epsilon_reachable_transitions.end(),
                                                     _nfa._transitions[nfa_state].begin(),
                                                     _nfa._transitions[nfa_state].end());
            }
            epsilon_reachable_transitions = normalize_transitions(std::move(epsilon_reachable_transitions));
            std::vector<dfa::transition> transitions_from_dfa_state;
            unsigned next_undefined_char = 0U;
            for (const nfa::transition& t : epsilon_reachable_transitions) {
                if (!t.is_epsilon()) {
                    SASSERT(next_undefined_char <= t._begin_char);
                    if (next_undefined_char < t._begin_char) {
                        transitions_from_dfa_state.push_back({ garbage_state(), next_undefined_char, t._begin_char });
                    }
                    next_undefined_char = t._end_char;
                    const std::set<unsigned>& nfa_targets = _nfa.epsilon_closure(t._to_states);
                    unsigned dfa_target = get_dfa_state(nfa_targets);
                    transitions_from_dfa_state.push_back({ dfa_target, t._begin_char, t._end_char });
                    if (0 == enqueued_dfa_states.count(dfa_target)) {
                        enqueued_dfa_states.insert(dfa_target);
                        nfa_state_sets_to_do.push(nfa_targets);
                    }
                }
            }
            if (next_undefined_char < alphabet_size) {
                transitions_from_dfa_state.push_back({ garbage_state(), next_undefined_char, alphabet_size });
            }
            _dfa_transitions[dfa_state] = transitions_from_dfa_state;
        }
        return dfa(0, _dfa_accept_states, _dfa_transitions);
    }
};

template<enum product_action product_action>
class dfa_product_builder {
    const dfa& _dfa0;
    const dfa& _dfa1;

    dfa::transitions _transitions;
    std::set<unsigned> _accept_states;
    std::map<std::pair<unsigned, unsigned>, unsigned> _state_map;

    unsigned get_state(unsigned s0, unsigned s1) {
        auto state_pair = std::make_pair(s0, s1);
        auto it = _state_map.find(state_pair);
        if (it != _state_map.end()) {
            return it->second;
        }
        unsigned new_state = _transitions.size();
        _transitions.push_back(std::vector<dfa::transition>());
        _state_map[state_pair] = new_state;
        switch (product_action) {
            case Intersect:
                if (0 < _dfa0._accept_states.count(s0)) {
                    if (0 < _dfa1._accept_states.count(s1)) {
                        _accept_states.insert(new_state);
                    }
                }
                break;
            case Union:
                if (0 < _dfa0._accept_states.count(s0)) {
                    _accept_states.insert(new_state);
                } else if (0 < _dfa1._accept_states.count(s1)) {
                    _accept_states.insert(new_state);
                }
                break;
            default:
                UNREACHABLE();
                break;
        }
        return new_state;
    }

    // Generate the product transitions from two vectors of transitions,
    // using _builder to generate the product of states.
    class transition_generator {
        const std::vector<dfa::transition>& _transitions_0;
        const std::vector<dfa::transition>& _transitions_1;
        unsigned _next_t0;
        unsigned _next_t1;
        unsigned _next_char;
        dfa_product_builder* _builder;
    public:
        transition_generator(const std::vector<dfa::transition>& transitions_0,
                             const std::vector<dfa::transition>& transitions_1,
                             dfa_product_builder* builder) :
            _transitions_0(transitions_0),
            _transitions_1(transitions_1),
            _next_t0(0U),
            _next_t1(0U),
            _next_char(0U),
            _builder(builder) {
            SASSERT(_builder != nullptr);
        }

        bool has_next() const { return _next_char < alphabet_size; }

        dfa::transition next(unsigned* s0, unsigned* s1) {
            SASSERT(has_next());
            SASSERT(s0 != nullptr);
            SASSERT(s1 != nullptr);
            SASSERT(_next_t0 < _transitions_0.size());
            SASSERT(_next_t1 < _transitions_1.size());
            const dfa::transition& t0 = _transitions_0[_next_t0];
            const dfa::transition& t1 = _transitions_1[_next_t1];
            *s0 = t0._to_states.get_state();
            *s1 = t1._to_states.get_state();
            unsigned next_char = std::min(t0._end_char, t1._end_char);
            dfa::transition t = { _builder->get_state(t0._to_states.get_state(), t1._to_states.get_state()), _next_char, next_char };
            _next_char = next_char;
            if (t1._end_char <= t0._end_char) {
                _next_t1++;
            }
            if (t0._end_char <= t1._end_char) {
                _next_t0++;
            }
            return t;
        }
    };

public:
    dfa_product_builder(const dfa& dfa0, const dfa& dfa1) : _dfa0(dfa0), _dfa1(dfa1) {}

    dfa build() {
        std::stack<std::pair<unsigned, unsigned>> states_to_do;
        std::set<unsigned> visited_product_states;

        unsigned start_product_state = get_state(_dfa0._start_state, _dfa1._start_state);
        states_to_do.push(std::make_pair(_dfa0._start_state, _dfa1._start_state));
        visited_product_states.insert(start_product_state);

        while (!states_to_do.empty()) {
            auto state_pair = states_to_do.top();
            states_to_do.pop();

            unsigned s0 = state_pair.first;
            unsigned s1 = state_pair.second;
            unsigned state = _state_map.find(state_pair)->second;

            transition_generator tg(_dfa0._transitions[s0], _dfa1._transitions[s1], this);
            std::vector<dfa::transition> new_transitions_from_state;
            while (tg.has_next()) {
                unsigned target_state_0;
                unsigned target_state_1;
                const dfa::transition& t = tg.next(&target_state_0, &target_state_1);
                new_transitions_from_state.push_back(t);
                if (visited_product_states.count(t._to_states.get_state()) == 0) {
                    visited_product_states.insert(t._to_states.get_state());
                    states_to_do.push(std::make_pair(target_state_0, target_state_1));
                }
            }
            _transitions[state] = new_transitions_from_state;
        }
        return _accept_states.empty() ? dfa::empty : dfa(start_product_state, std::move(_accept_states), std::move(_transitions));
    }
};

dfa dfa::complement() const {
    if (_transitions.size() == _accept_states.size()) {
        return empty;
    }
    std::set<unsigned> accept_states;
    for (unsigned i = 0; i < _transitions.size(); i++) {
        if (_accept_states.count(i) == 0) {
            accept_states.insert(i);
        }
    }
    return dfa(_start_state, accept_states, dfa::transitions(_transitions));
}

dfa dfa::disjunct(const dfa& other) const {
    return dfa_product_builder<Union>(*this, other).build().compact();
}

dfa dfa::intersect(const dfa& other) const {
    return dfa_product_builder<Intersect>(*this, other).build().compact();
}

// Return the transition relation of the reverse language accepted by this dfa.
// The result is an nfa transition relation as in a dfa two nodes can make a
// transition to a third node, thus the reverse transitions are
// non-deterministic
static nfa::transitions reverse_transitions(const dfa::transitions& dfa_transitions) {
    const unsigned size = dfa_transitions.size();
    nfa::transitions result(size);
    for (unsigned source = 0U; source < size; source++) {
        for (const auto& transition : dfa_transitions[source]) {
            for (const unsigned target : transition._to_states) {
                std::vector<nfa::transition>* new_transitions = &result[target];
                new_transitions->push_back({ std::vector<unsigned>(1, source), transition._begin_char, transition._end_char});
            }
        }
    }
    return nfa::normalize_transitions_map(result);
}

// compute as intersect bs and as - bs.
static void intersect_and_diff(const std::vector<unsigned>& as, const std::vector<unsigned>& bs, std::vector<unsigned>* intersect, std::vector<unsigned>* diff) {
    SASSERT(intersect != nullptr);
    SASSERT(diff != nullptr);
    SASSERT(check_ordered(as, std::less<unsigned>()));
    SASSERT(check_ordered(bs, std::less<unsigned>()));
    unsigned bs_index = 0U;
    for (unsigned a : as) {
        for (; bs_index < bs.size() && bs[bs_index] < a; bs_index++);
        if (bs_index < bs.size()) {
            unsigned b = bs[bs_index];
            if (b == a) {
                intersect->push_back(a);
                bs_index++;
            } else {
                SASSERT(a < b);
                diff->push_back(a);
            }
        } else {
            diff->push_back(a);
        }
    }
}

dfa dfa::compact() const {
    // Hopcroft 1971: http://i.stanford.edu/pub/cstr/reports/cs/tr/71/190/CS-TR-71-190.pdf
    // https://en.wikipedia.org/wiki/DFA_minimization#Hopcroft's_algorithm

    if (_is_compact) {
        return *this;
    }
    if (_transitions.size() < 2) {
        return dfa(_start_state, _accept_states, _transitions, true /* is_compact */);
    }
    if (_accept_states.size() == 0 || _accept_states.size() == _transitions.size()) {
        transition t = { 0, 0, alphabet_size };
        std::set<unsigned> accept_states;
        if (_accept_states.size() == _transitions.size()) {
            accept_states.insert(0);
        }
        return dfa(0, accept_states, std::vector<std::vector<transition>>(1, std::vector<transition>(1, t)), true /* is_compact */);
    }

    std::vector<unsigned> state_to_equivalence_class(_transitions.size(), 0U);
    std::vector<std::vector<unsigned>> equivalence_classes(2, std::vector<unsigned>());

    for (unsigned state = 0U; state < _transitions.size(); state++) {
        unsigned index = _accept_states.count(state) != 0 ? 0U : 1U;
        equivalence_classes[index].push_back(state);
        state_to_equivalence_class[state] = index;
    }

    std::stack<unsigned> equivalence_classes_to_do;
    equivalence_classes_to_do.push(0);

    const nfa::transitions& reverse_transitions_map = reverse_transitions(_transitions);

    while (!equivalence_classes_to_do.empty()) {
        const unsigned equiv_class = equivalence_classes_to_do.top();
        equivalence_classes_to_do.pop();

        std::vector<nfa::transition> reverse_transitions_from_equiv_class;
        for (unsigned state : equivalence_classes[equiv_class]) {
            reverse_transitions_from_equiv_class.insert(reverse_transitions_from_equiv_class.end(),
                                                        reverse_transitions_map[state].begin(),
                                                        reverse_transitions_map[state].end());
        }
        reverse_transitions_from_equiv_class = normalize_transitions(std::move(reverse_transitions_from_equiv_class));
        for (const nfa::transition& reverse_transition : reverse_transitions_from_equiv_class) {
            // Every state in states_with_transitions_to_equiv_class class makes a transition to a state in equiv_class
            const std::vector<unsigned>& states_with_transitions_to_equiv_class = reverse_transition._to_states;
            for (const unsigned state : states_with_transitions_to_equiv_class) {
                const unsigned equivalence_class = state_to_equivalence_class[state];
                SASSERT(equivalence_class < equivalence_classes.size());
                std::vector<unsigned> equiv_class_intersect;
                std::vector<unsigned> equiv_class_diff;
                intersect_and_diff(equivalence_classes[equivalence_class],
                                   states_with_transitions_to_equiv_class,
                                   &equiv_class_intersect,
                                   &equiv_class_diff);
                if (!equiv_class_intersect.empty() && !equiv_class_diff.empty()) {
                    if (equiv_class_intersect.size() < equiv_class_diff.size()) {
                        equivalence_classes[equivalence_class] = std::move(equiv_class_diff);
                        equivalence_classes.push_back(std::move(equiv_class_intersect));
                    } else {
                        equivalence_classes[equivalence_class] = std::move(equiv_class_intersect);
                        equivalence_classes.push_back(std::move(equiv_class_diff));
                    }
                    const unsigned new_equivalence_class = equivalence_classes.size() - 1;
                    for (const unsigned state : equivalence_classes[new_equivalence_class]) {
                        SASSERT(state_to_equivalence_class[state] == equivalence_class);
                        state_to_equivalence_class[state] = new_equivalence_class;
                    }
                    equivalence_classes_to_do.push(new_equivalence_class);
                }
            }
        }
    }

    if (equivalence_classes.size() < _transitions.size()) {
        std::set<unsigned> new_accepted_states;
        for (unsigned state : _accept_states) {
            new_accepted_states.insert(state_to_equivalence_class[state]);
        }
        transitions new_transitions_map(equivalence_classes.size());
        for (unsigned new_state = 0U; new_state < equivalence_classes.size(); new_state++) {
            const std::vector<unsigned>& equivalent_states = equivalence_classes[new_state];
            SASSERT(!equivalent_states.empty());
            unsigned old_state = equivalent_states[0];
            std::vector<transition> new_transitions;
            for (const transition& old_transition : _transitions[old_state]) {
                if (new_transitions.empty() ||
                    new_transitions[new_transitions.size() - 1]._to_states.get_state() != state_to_equivalence_class[old_transition._to_states.get_state()]) {
                    new_transitions.push_back(
                        { state_to_equivalence_class[old_transition._to_states.get_state()],
                          old_transition._begin_char,
                          old_transition._end_char }
                    );
                } else {
                    new_transitions[new_transitions.size() - 1]._end_char = old_transition._end_char;
                }
            }
            new_transitions_map[new_state] = new_transitions;
        }
        return dfa(state_to_equivalence_class[_start_state], new_accepted_states, new_transitions_map, true /* is_compact */);
    } else {
        SASSERT(equivalence_classes.size() == _transitions.size());
        return dfa(_start_state, _accept_states, _transitions, true /* is_compact */);
    }
}

zstring dfa::get_string() const {
    std::stack<std::pair<unsigned, transition>> to_do;
    std::set<dfa_target> visited_states;

    if (_accept_states.count(_start_state) != 0) {
        return zstring();
    }

    unsigned index = 0U;

    class {
    private:
        const std::array<transition, 7> priorties = {{
            { 0, 'A', 'Z' + 1 },
            { 0, 'a', 'z' + 1 },
            { 0, '0', '9' + 1},
            { 0, '!', '~' + 1 },
            { 0, 0xa1, 0x100 },
            { 0, 0x20, alphabet_size },
            { 0, 0x0, alphabet_size }
        }};
        bool intersects(const transition& a, const transition& b) const {
            return !(a._end_char <= b._begin_char || b._end_char <= a._begin_char);
        }
        unsigned rank(const transition& t) const {
            unsigned r = 0;
            for (const auto& tt : priorties) {
                if (intersects(tt, t)) return r;
                r++;
            }
            return r;
        }
    public:
        bool operator()(const transition& a, const transition& b) const {
            return rank(a) < rank(b);
        }

        unsigned best_char(const transition& t) const {
            for (const auto& tt : priorties) {
                if (intersects(tt, t)) {
                    return std::max(tt._begin_char, t._begin_char);
                }
            }
            return t._begin_char;
        }
    } prefered_transition_order;

    visited_states.insert(dfa_target(_start_state));
    std::vector<transition> sorted_transitions(_transitions[_start_state]);
    std::sort(sorted_transitions.begin(), sorted_transitions.end(), prefered_transition_order);
    for (const transition& t : sorted_transitions) {
        to_do.push(std::make_pair(index, t));
    }

    std::vector<unsigned> string;

    while (!to_do.empty()) {
        index = to_do.top().first;
        const transition t = to_do.top().second;
        to_do.pop();

        if (visited_states.count(t._to_states) != 0) {
            continue;
        }
        visited_states.insert(t._to_states);

        if (index < string.size()) {
            string[index] = prefered_transition_order.best_char(t);
        } else {
            SASSERT(index == string.size());
            string.push_back(prefered_transition_order.best_char(t));
        }
        index++;

        if (_accept_states.count(t._to_states.get_state()) != 0) {
            return zstring(index, string.data());
        }

        std::vector<transition> sorted_transitions(_transitions[t._to_states.get_state()]);
        std::sort(sorted_transitions.begin(), sorted_transitions.end(), prefered_transition_order);
        for (const transition& tt : sorted_transitions) {
            to_do.push(std::make_pair(index, tt));
        }
    }
    UNREACHABLE();
    return zstring();
}

#ifdef Z3DEBUG
bool dfa::check_invariant() const {
    unsigned number_of_states = _transitions.size();
    SASSERT(_start_state < number_of_states);
    for (unsigned s : _accept_states) {
        SASSERT(s < number_of_states);
    }
    for (const std::vector<transition>& transitions : _transitions) {
        unsigned next_char = 0;
        for (const transition& t : transitions) {
            SASSERT(t.check_invariant());
            SASSERT(t._begin_char == next_char);
            SASSERT(t._end_char <= alphabet_size);
            next_char = t._end_char;
            SASSERT(t._to_states.get_state() < number_of_states);
        }
        SASSERT(next_char == alphabet_size);
    }
    return true;
}
#endif // def Z3DEBUG

dfa::dfa(unsigned start_state,
         const std::set<unsigned>& accept_states,
         const transitions& transitions,
         bool is_compact) :
    automaton<dfa_target>(start_state, accept_states, transitions), _is_compact(is_compact) {
    SASSERT(check_invariant());
}

nfa::nfa() : automaton<std::vector<unsigned>>(empty._start_state, empty._accept_states, empty._transitions) {
    SASSERT(check_invariant());
}

dfa::dfa() : automaton<dfa_target>(empty._start_state, empty._accept_states, empty._transitions), _is_compact(empty._is_compact) {
    SASSERT(check_invariant());
}

static std::string pretty(unsigned x) {
    if (('#' <= x && x <= '~') || x == '!') return std::string(1, x);
    if (x == '"') return std::string("\\\"");
    std::stringstream sstream;
    sstream << "\\\\x" << std::hex << x;
    return std::string(sstream.str());
}

template<typename T>
std::ostream& automaton<T>::pp(std::ostream& out) const {
    out << "digraph {" << std::endl;
    std::string indent1(4, ' ');
    std::string indent2(8, ' ');
    out << indent1 << "{" << std::endl;
    for (unsigned state = 0; state < _transitions.size(); state++) {
        std::string fill = "";
        if (state == _start_state) {
            fill = " style=filled fillcolor=yellow";
        }
        std::string shape = " shape=circle";
        if (0 < _accept_states.count(state)) {
            shape = " shape=doublecircle";
        }
        out << indent2 << state << " [" << fill << shape << " ]" << std::endl;
    }
    out << indent1 << "}" << std::endl;
    for (unsigned from_state = 0U; from_state < _transitions.size(); from_state++) {
        for (const transition_t<T>& t : _transitions[from_state]) {
            out << indent1 << from_state << " -> {";
            for (unsigned target : t._to_states) {
                out << " " << target;
            }
            out << " } [label=";
            if (t.is_epsilon()) {
                out << "<&epsilon;>";
            } else if (t._begin_char == t._end_char - 1) {
                out << '"' << pretty(t._begin_char) << '"';
            } else {
                out << '"' << '[' << pretty(t._begin_char) << " - " << pretty(t._end_char - 1) << ']' << '"';
            }
            out << "]" << std::endl;
        }
    }
    out << "}" << std::endl;
    return out;
}

dfa nfa::get_dfa() const {
    return dfa_builder(*this).get_dfa();
}

nfa::transition nfa::make_epsilon_transition(unsigned tgt) {
    return { std::vector<unsigned>(1, tgt), transition::epsilon_char, transition::epsilon_char };
}

nfa nfa::from_range(unsigned start, unsigned end, ast_manager& m) {
    if (start <= end) {
        if (end < alphabet_size) {
            transitions transitions(2);
            transition t = { std::vector<unsigned>(1, 1), start, end + 1 };
            transitions[0] = std::vector<transition>(1, t);
            std::set<unsigned> accept_states;
            accept_states.insert(1);
            return nfa(0U, accept_states, transitions);
        }
        m.raise_exception("re.range outside alphabet");
    }
    return empty;
}

nfa nfa::from_string(const zstring& str) {
    TRACE("automata", tout << "nfa::from_string(\"" << str.encode() << "\")";);
    unsigned size = str.length() + 1;
    transitions transitions(size);
    for (unsigned i = 0; i < size - 1; ++i) {
        transition t = { std::vector<unsigned>(1, i + 1), str[i], str[i] + 1 };
        transitions[i] = std::vector<transition>(1, t);
    }
    std::set<unsigned> accept_states;
    accept_states.insert(size - 1);
    return nfa(0U, accept_states, transitions);
}

nfa nfa::all_char() {
    transition t = { std::vector<unsigned>(1, 1U), 0, alphabet_size };
    transitions transitions(2U);
    transitions[0] = std::vector<transition>(1, t);
    std::set<unsigned> accept_states;
    accept_states.insert(1U);
    return nfa(0, accept_states, transitions);
}

nfa nfa::all() {
    transition t = { std::vector<unsigned>(1, 0U), 0, alphabet_size };
    transitions transitions(1U, std::vector<transition>(1, t));
    std::set<unsigned> accept_states;
    accept_states.insert(0U);
    return nfa(0, accept_states, transitions);
}

void nfa::add_transition(transitions* transition_map, unsigned from, const transition& t) {
    SASSERT(transition_map != nullptr);
    SASSERT(from < transition_map->size());
#ifdef Z3DEBUG
    for (unsigned s : t._to_states) {
        SASSERT(s < transition_map->size());
    }
#endif // def Z3DEBUG
    (*transition_map)[from].push_back(t);
}

const nfa nfa::empty = nfa(0U, std::set<unsigned>(), std::vector<std::vector<transition>>(1));

const dfa dfa::empty = nfa::empty.get_dfa().compact();

nfa nfa::append(const nfa& other) const {
    if (_accept_states.empty()) return empty;

    transitions new_transitions(_transitions.size() + other._transitions.size());
    for (unsigned state = 0U; state < _transitions.size(); state++) {
        new_transitions[state] = _transitions[state];
    }
    for (unsigned state = 0U; state < other._transitions.size(); state++) {
        new_transitions[_transitions.size() + state] = shift_transitions(other._transitions[state], _transitions.size());
    }

    std::set<unsigned> new_accept_states;
    for (unsigned accept_state : other._accept_states) {
        new_accept_states.insert(accept_state + _transitions.size());
    }

    // Add epsilon transitions to other._start_state
    for (unsigned accept_state : _accept_states) {
        add_transition(&new_transitions, accept_state, make_epsilon_transition(_transitions.size() + other._start_state));
    }

    return nfa(_start_state, new_accept_states, new_transitions);
}

nfa::transition nfa::shift_transition(const nfa::transition& t, unsigned by) {
    std::vector<unsigned> to_states(t._to_states.size());
    for (unsigned i = 0U; i < t._to_states.size(); i++) {
        to_states[i] = t._to_states[i] + by;
    }
    return { to_states, t._begin_char, t._end_char };
}

std::vector<nfa::transition> nfa::shift_transitions(const std::vector<transition>& ts, unsigned by) {
    std::vector<transition> new_transitions(ts.size());
    for (unsigned i = 0; i < ts.size(); i++) {
        new_transitions[i] = shift_transition(ts[i], by);
    }
    return new_transitions;
}

nfa nfa::disjunct(const nfa& other) const {
    transitions new_transitions(_transitions.size() + other._transitions.size() + 1U);

    // Epsilon transition from 0 to _start_state shifted by 1 and other._start_state shifted by _transitions.size() + 1
    std::vector<unsigned> epsilon_targets(2);
    epsilon_targets[0] = _start_state + 1U;
    epsilon_targets[1] = _transitions.size() + 1U + other._start_state;

    new_transitions[0] = std::vector<transition>(1, { epsilon_targets, transition::epsilon_char, transition::epsilon_char });

    for (unsigned state = 0U; state < _transitions.size(); state++) {
        new_transitions[state + 1] = shift_transitions(_transitions[state], 1);
    }
    for (unsigned other_state = 0; other_state < other._transitions.size(); other_state++) {
        new_transitions[other_state + _transitions.size() + 1] = shift_transitions(other._transitions[other_state], _transitions.size() + 1);
    }

    std::set<unsigned> new_accept_states;
    for (unsigned accept_state : _accept_states) {
        new_accept_states.insert(accept_state + 1);
    }
    for (unsigned accept_state : other._accept_states) {
        new_accept_states.insert(accept_state + _transitions.size() + 1);
    }

    return nfa(0, new_accept_states, new_transitions);
}

nfa nfa::opt() const {
    if (_accept_states.count(_start_state) != 0) {
        return *this;
    }
    transitions transitions(_transitions);
    unsigned state = transitions.size();
    transitions.push_back(std::vector<transition>(1, make_epsilon_transition(_start_state)));
    std::set<unsigned> accept_states(_accept_states);
    accept_states.insert(state);
    return nfa(state, accept_states, transitions);
}

nfa nfa::plus() const {
    transitions transitions(_transitions);
    for (unsigned accept_state : _accept_states) {
        transitions[accept_state].push_back(make_epsilon_transition(_start_state));
    }
    return nfa(_start_state, _accept_states, transitions);
}

nfa nfa::star() const {
    return opt().plus();
}

} /* namespace automata */

theory_automata::theory_automata(ast_manager& m):
    theory(m.mk_family_id("seq" /* "seq" is required to get string theory symbols registered with this theory */ )),
    m(m),
    m_trail_stack(*this),
    m_util(m) {
}

final_check_status theory_automata::final_check_eh() {
    TRACE("automata_verbose", tout << "theory_automata::final_check_eh" << std::endl;);
    return FC_DONE;
}

/*
 * Given an interned expression (an expression with an enode),
 * create a theory variable for the expression if not previously done.
 */
theory_var theory_automata::mk_var(enode* n) {
    if (!m_util.is_seq(n->get_owner()) &&
        !m_util.is_re(n->get_owner())) {
        return null_theory_var;
    }
    if (is_attached_to_var(n)) {
        return n->get_th_var(get_id());
    }
    theory_var v = theory::mk_var(n);
    get_context().attach_th_var(n, this, v);
    return v;
}

/*
 * Internalize an equality. Make the least set of necessary theory variables:
 * Make a boolean variable for the equality and make theory variables for each
 * argument to the equality, e.g, for S = R, make theory variables for both S
 * and R, but not sub-expressions of S and R.  If S or R is an uninterpreted
 * function symbol, then add it to m_automata_per_var. This function can be
 * called doing proof search, as we create literals for equilities.
 */
void theory_automata::internalize_eq_eh(app* atom, bool_var v) {
    TRACE("automata_verbose", tout << "internalize_eq_eh: " << v << " and " << mk_pp(atom, m) << std::endl;);
    context& ctx = get_context();

    if (!ctx.e_internalized(atom)) {
        internalize_term(atom);
        bool_var bv = ctx.mk_bool_var(atom);
        ctx.set_var_theory(bv, get_id());
        ctx.mark_as_relevant(bv);
    }
    for (expr* e : *atom) {
        if (m_util.str.is_string_term(e)) {
            mk_var(ensure_enode(e));
            if (is_uninterp_const(e)) {
                ensure_entry_for_var(e);
            }
        } else {
            m.raise_exception("equation on non-string terms");
        }
    }
}

/*
 * Internalize string theory atomic propositions.
 * Make theory variables for each string argument to the atom, e.g, for str.in.re S R,
 * make a theory variable for S. Make a boolean variable for the atomic proposition.
 */
bool theory_automata::internalize_atom(app* atom, bool gated) {
    TRACE("automata_verbose", tout << "internalize (gated: " << gated << "): " << mk_pp(atom, m) << std::endl;);
    context& ctx = get_context();

    if (!ctx.e_internalized(atom)) {
        internalize_term(atom);
        bool_var bv = ctx.mk_bool_var(atom);
        ctx.set_var_theory(bv, get_id());
        ctx.mark_as_relevant(bv);
    }
    for (expr* e : *atom) {
        if (m_util.str.is_string_term(e)) {
            mk_var(ensure_enode(e));
            if (is_uninterp_const(e)) {
                ensure_entry_for_var(e);
            }
        }
    }
    return true;
}

void theory_automata::ensure_entry_for_var(expr* e) {
    SASSERT(is_uninterp_const(e));
    if (!m_automata_per_var.contains(e)) {
        context& ctx = get_context();
        scoped_vector<std::pair<literal, automata::dfa>> v;
        unsigned missing_levels = ctx.get_scope_level() - ctx.get_base_level();
        for (unsigned i = 0; i < missing_levels; i++) {
            v.push_scope();
        }
        m_automata_per_var.insert(e, v);
    }
}

enode* theory_automata::ensure_enode(expr* e) {
    context& ctx = get_context();
    if (!ctx.e_internalized(e)) {
        ctx.internalize(e, false);
    }
    return ctx.get_enode(e);
}

bool theory_automata::theory_automata::internalize_term(app* term) {
    context& ctx = get_context();

    for (expr* arg : *term) {
        ensure_enode(arg);
    }

    if (!ctx.e_internalized(term)) {
        TRACE("automata_verbose", tout << mk_pp(term, m) << std::endl;);
        ctx.mk_enode(term, false, m.is_bool(term), true);
    }

    return true;
}

void theory_automata::apply_sort_cnstr(enode* n, sort* s) {
    TRACE("automata_verbose", tout << "apply_sort_cnstr " << s->get_name() << " to " << mk_pp(n->get_owner(), m)  << std::endl;);
}

void theory_automata::new_eq_eh(theory_var v0, theory_var v1) {
    expr* e0 = get_enode(v0)->get_owner();
    expr* e1 = get_enode(v1)->get_owner();
    TRACE("automata", tout << "theory_automata::new_eq_eh: " << mk_pp(e0, m) << " == " << mk_pp(e1, m) << std::endl;);
    if (!m_util.str.is_string_term(e0) || !m_util.str.is_string_term(e1)) {
        m.raise_exception("Equation on non-string terms");
    }
    if (!is_uninterp_const(e0)) {
        expr* e_tmp = e0;
        e0 = e1;
        e1 = e_tmp;
    }
    literal l = ~mk_eq(e0, e1, false);
    symbol s1;
    if (is_uninterp_const(e1)) {
        m.raise_exception("Aliasing equation not supported");
    } else if (m_util.str.is_string(e1, s1)) {
        if (is_uninterp_const(e0)) {
            string_must_be_in(e0, e1, l);
        }
    } else {
        m.raise_exception("Equation not supported");
    }
}

void theory_automata::new_diseq_eh(theory_var v0, theory_var v1) {
    expr* e0 = get_enode(v0)->get_owner();
    expr* e1 = get_enode(v1)->get_owner();
    TRACE("automata", tout << "theory_automata::new_diseq_eh: " << mk_pp(e0, m) << " != " << mk_pp(e1, m) << std::endl;);
    if (!m_util.str.is_string_term(e0) || !m_util.str.is_string_term(e1)) {
        m.raise_exception("Equation on non-string terms");
    }
    if (!is_uninterp_const(e0)) {
        expr* e_tmp = e0;
        e0 = e1;
        e1 = e_tmp;
    }
    literal l = mk_eq(e0, e1, false);
    symbol s1;
    if (is_uninterp_const(e1)) {
        m.raise_exception("Non-aliasing equation not supported");
    } else if (m_util.str.is_string(e1, s1)) {
        if (is_uninterp_const(e0)) {
            string_must_be_in(e0, e1, l);
        }
    } else {
        m.raise_exception("Non-aliasing equation not supported");
    }
}

static automata::dfa compact_and_negate_if_needed(const automata::dfa& aut, bool do_it) {
    if (do_it) {
        return aut.complement().compact();
    } else {
        return aut.compact();
    }
}

void theory_automata::string_must_be_in(expr* string, expr* pattern, literal l) {
    context& ctx = get_context();

    if (is_uninterp_const(string)) {
        automata::dfa daut = compact_and_negate_if_needed(get_dfa(pattern), !l.sign());
        TRACE("automata", tout << mk_pp(string, m) << " dfa for expression: " << mk_pp(pattern, m) << " " << (l.sign() ? "true" : "false") << std::endl; daut.pp(tout) <<std::endl;);
        if (daut.is_empty()) {
            ctx.mk_th_axiom(get_id(), 1, &l);
        }
        SASSERT(m_automata_per_var.contains(string));
        scoped_vector<std::pair<literal, automata::dfa>>& e_automatas = m_automata_per_var[string];
        if (e_automatas.empty()) {
            TRACE("automata", tout << "first automata" << std::endl; daut.pp(tout) << std::endl;);
            e_automatas.push_back(std::make_pair(l, daut));
        } else {
            const automata::dfa& last_daut = e_automatas[e_automatas.size() - 1].second;
            SASSERT(!last_daut.is_empty());
            const automata::dfa& combined_daut = last_daut.intersect(daut).compact();
            if (combined_daut.is_empty()) {
                TRACE("automata", tout << "combined automata is empty" << std::endl;);
                literal literals[e_automatas.size() + 1];
                unsigned index = 0U;
                for (const auto& p : e_automatas) {
                    literals[index++] = p.first;
                }
                literals[index] = l;
                ctx.mk_th_axiom(get_id(), e_automatas.size() + 1, literals);
            } else {
                TRACE("automata", tout << "combined automata" << std::endl; combined_daut.pp(tout) << std::endl;);
                e_automatas.push_back(std::make_pair(l, combined_daut));
            }
        }
    } else {
        TRACE("automata", tout << "Not an uninterpreted function symbol: " << mk_pp(string, m) << std::endl;);
        m.raise_exception("String contraints on something not an uninterpreted function symbol");
    }
}

void theory_automata::assign_eh(bool_var v, bool is_true) {
    context& ctx = get_context();
    expr* e = ctx.bool_var2expr(v);
    TRACE("automata", tout << "assign: " << (is_true ? "true" : "false") << " to: " << mk_pp(e, m)  << std::endl;);

    expr* e0;
    expr* e1;
    literal l(v, is_true);
    if (m_util.str.is_in_re(e, e0, e1)) {
        string_must_be_in(e0, e1, l);
    } else if (m_util.str.is_suffix(e, e0, e1)) {
        expr* all = m_util.re.mk_full_seq(m_util.re.mk_re(m.get_sort(e0)));
        expr* symbol = m_util.re.mk_to_re(e0);
        expr_ref string(m_util.re.mk_concat(all, symbol), m);
        string_must_be_in(e1, string, l);
    } else if (m_util.str.is_prefix(e, e0, e1)) {
        expr* all = m_util.re.mk_full_seq(m_util.re.mk_re(m.get_sort(e0)));
        expr* symbol = m_util.re.mk_to_re(e0);
        expr_ref string(m_util.re.mk_concat(symbol, all), m);
        string_must_be_in(e1, string, l);
    } else if (m_util.str.is_contains(e, e0, e1)) {
        expr* all = m_util.re.mk_full_seq(m_util.re.mk_re(m.get_sort(e0)));
        expr* symbol = m_util.re.mk_to_re(e1);
        expr_ref contains(m_util.re.mk_concat(all, m_util.re.mk_concat(symbol, all)), m);
        string_must_be_in(e0, contains, l);
    } else {
        NOT_IMPLEMENTED_YET();
    }
}

automata::dfa theory_automata::get_dfa(expr* e) {
    automata::dfa aut;
    if (m_dfa_cache.find(e, aut)) {
        return aut;
    }
    aut = get_nfa(e).get_dfa().compact();
    m_dfa_cache.insert(e, aut);
    m.inc_ref(e);
    return aut;
}

automata::nfa theory_automata::get_nfa(expr* e) {
    expr* e0;
    expr* e1;
    unsigned n1, n2;

    automata::nfa aut;
    if (m_nfa_cache.find(e, aut)) {
        return aut;
    }

    if (m_util.str.is_string(e)) {
        zstring s;
        m_util.str.is_string(e, s);
        aut = automata::nfa::from_string(s);
    } else if (m_util.re.is_to_re(e, e0)) {
        SASSERT(m_util.str.is_string(e0));
        zstring s;
        m_util.str.is_string(e0, s);
        aut = automata::nfa::from_string(s);
    } else if (m_util.re.is_concat(e, e0, e1)) {
        aut = get_nfa(e0).append(get_nfa(e1));
    } else if (m_util.re.is_union(e, e0, e1)) {
        aut = get_nfa(e0).disjunct(get_nfa(e1));
    } else if (m_util.re.is_intersection(e, e0, e1)) {
        aut = get_dfa(e0).intersect(get_dfa(e1)).get_nfa();
    } else if (m_util.re.is_complement(e, e0)) {
        aut = get_dfa(e0).complement().get_nfa();
    } else if (m_util.re.is_star(e, e0)) {
        aut = get_nfa(e0).star();
    } else if (m_util.re.is_plus(e, e0)) {
        aut = get_nfa(e0).plus();
    } else if (m_util.re.is_opt(e, e0)) {
        aut = get_nfa(e0).opt();
    } else if (m_util.re.is_range(e, e0, e1)) {
        zstring s0;
        zstring s1;
        if (m_util.str.is_string(e0, s0) && m_util.str.is_string(e1, s1) && s0.length() == 1 && s1.length() == 1) {
            unsigned c0 = s0[0];
            unsigned c1 = s1[0];
            aut = automata::nfa::from_range(c0, c1, m);
        } else {
            m.raise_exception("re.range with non-supported arguments");
        }
    } else if (m_util.re.is_loop(e, e0, n1, n2)) {
        const automata::nfa& a = get_nfa(e0);
        const automata::nfa& a_opt = a.opt();
        const zstring s;
        aut = automata::nfa::from_string(s);
        for (unsigned i = 0; i < n1; i++) {
            aut = aut.append(a);
        }
        for (unsigned i = n1; i < n2; i++) {
            aut = aut.append(a_opt);
        }
    } else if (m_util.re.is_loop(e, e0, n1)) {
        const automata::nfa& a = get_nfa(e0);
        const automata::nfa& a_star = a.star();
        const zstring s;
        aut = automata::nfa::from_string(s);
        for (unsigned i = 0; i < n1; i++) {
            aut = aut.append(a);
        }
        aut = aut.append(a_star);
    } else if (m_util.re.is_empty(e)) {
        aut = automata::nfa::empty;
    } else if (m_util.re.is_full_char(e)) {
        aut = automata::nfa::all_char();
    } else if (m_util.re.is_full_seq(e)) {
        aut = automata::nfa::all();
    } else {
        TRACE("automata", tout << mk_pp(e, m););
        NOT_IMPLEMENTED_YET();
    }

    m_nfa_cache.insert(e, aut);
    m.inc_ref(e);
    return aut;
}

void theory_automata::relevant_eh(app* n) {
    TRACE("automata_verbose", tout << "relevant_eh:  " << mk_pp(n, m) << std::endl;);
}

void theory_automata::push_scope_eh() {
    TRACE("automata", tout << "theory_automata::push_scope_eh" << std::endl;);
    theory::push_scope_eh();
    for (auto&& automata_vector : m_automata_per_var) {
        automata_vector.m_value.push_scope();
    }
}

void theory_automata::pop_scope_eh(unsigned num_scopes) {
    TRACE("automata", tout << "theory_automata::pop_scope_eh: " << num_scopes << std::endl;);

    for (auto&& automata_vector : m_automata_per_var) {
        automata_vector.m_value.pop_scope(num_scopes);
    }
    theory::pop_scope_eh(num_scopes);
}

void theory_automata::add_theory_assumptions(expr_ref_vector & assumptions) {
    TRACE("automata", tout << "theory_automata::add_theory_assumptions" << std::endl;);
}

void theory_automata::init_search_eh() {
    TRACE("automata", tout << "theory_automata::init_search_eh" << std::endl;);
}

void theory_automata::propagate() {
    TRACE("automata", tout << "theory_automata::propagate" << std::endl;);
}

void theory_automata::restart_eh() {
    TRACE("automata_verbose", tout << "theory_automata::restart_eh" << std::endl;);
}

model_value_proc* theory_automata::mk_value(enode* n, model_generator& mg) {
    TRACE("automata", tout << "mk_value for: " << mk_pp(n->get_owner(), m) << std::endl;);

    context& ctx = get_context();
    SASSERT(ctx.e_internalized(n->get_owner()));
    expr* e = n->get_owner();
    if (m_automata_per_var.contains(e)) {
        const auto& daut_vector = m_automata_per_var[e];
        const automata::dfa& daut = daut_vector[daut_vector.size() - 1].second;
        const zstring& s = daut.get_string();
        return alloc(expr_wrapper_proc, to_app(m_util.str.mk_string(s)));
    } else if (is_uninterp_const(e)) {
        // Shouldn't happen, so lets crash if it does
        m.raise_exception("internal error");
        UNREACHABLE();
    } else if (m_util.str.is_string(e)) {
        return alloc(expr_wrapper_proc, to_app(e));
    }
    return nullptr;
}

class automata_value_factory : public value_factory {
    typedef hashtable<symbol, symbol_hash_proc, symbol_eq_proc> symbol_set;

    seq_util u;
    symbol_set m_strings;
    std::string delim;
    unsigned m_next;
public:
    automata_value_factory(ast_manager & m, family_id fid) :
        value_factory(m, fid),
        u(m), delim("!"), m_next(0) {}
    ~automata_value_factory() override {}
    expr * get_some_value(sort * s) override {
        return u.str.mk_string(symbol("some value"));
    }
    bool get_some_values(sort * s, expr_ref & v1, expr_ref & v2) override {
        v1 = u.str.mk_string(symbol("value 1"));
        v2 = u.str.mk_string(symbol("value 2"));
        return true;
    }
    expr * get_fresh_value(sort * s) override {
        if (u.is_string(s)) {
            while (true) {
                std::ostringstream strm;
                strm << delim << std::hex << (m_next++) << std::dec << delim;
                symbol sym(strm.str().c_str());
                if (m_strings.contains(sym)) continue;
                m_strings.insert(sym);
                return u.str.mk_string(sym);
            }
        }
        sort* seq = nullptr;
        if (u.is_re(s, seq)) {
            expr* v0 = get_fresh_value(seq);
            return u.re.mk_to_re(v0);
        }
        UNREACHABLE();
        return nullptr;
    }
    void register_value(expr * n) override {
        symbol s;
        if (u.str.is_string(n, s)) {
            m_strings.insert(s);
        }
    }
};

void theory_automata::init_model(model_generator& mg) {
    mg.register_factory(alloc(automata_value_factory, m, get_family_id()));
}

theory_automata::~theory_automata() {
    for (auto&& x : m_nfa_cache) {
        m.dec_ref(&x.get_key());
    }
    for (auto&& x : m_dfa_cache) {
        m.dec_ref(&x.get_key());
    }
    m_trail_stack.reset();
}

} /* namespace smt */
