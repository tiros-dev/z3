/*++
Module Name:

    theory_automata.h

Abstract:

    <abstract>

Author:

    Carsten Varming (varming) 2018-03-15

Revision History:

--*/
#ifndef THEORY_AUTOMATA_H_
#define THEORY_AUTOMATA_H_

#include <climits>
#include <set>
#include <vector>
#include "ast/seq_decl_plugin.h"
#include "smt/smt_context.h"
#include "smt/smt_model_generator.h"
#include "smt/smt_theory.h"
#include "smt/smt_types.h"
#include "util/debug.h"
#include "util/obj_pair_hashtable.h"
#include "util/scoped_vector.h"

namespace smt {

namespace automata {

template<typename TransitionTarget>
struct transition_t {
    TransitionTarget _to_states;
    unsigned _begin_char;
    unsigned _end_char; // Transision on [m_begin_char .. m_end_char - 1]

    static const unsigned max_end_char = UINT_MAX;
    static const unsigned epsilon_char = UINT_MAX;

    bool is_epsilon() const {
        return _begin_char == epsilon_char && _end_char == epsilon_char;
    }

#ifdef Z3DEBUG
    bool check_invariant() const {
        SASSERT(_begin_char < _end_char || is_epsilon());
        return true;
    };
#endif // def Z3DEBUG
};

class dfa_builder;

enum product_action {
    Intersect,
    Union
};

template<enum product_action product_action>
class dfa_product_builder;

template<typename TransitionTarget>
class automaton {
    friend dfa_builder;
protected:
    unsigned _start_state;
    std::set<unsigned> _accept_states;
    std::vector<std::vector<transition_t<TransitionTarget>>> _transitions;

    automaton(unsigned start_state,
              const std::set<unsigned>& accept_states,
              const std::vector<std::vector<transition_t<TransitionTarget>>>& transitions) :
        _start_state(start_state),
        _accept_states(accept_states),
        _transitions(transitions) {
    }
};

class nfa;

class dfa: public automaton<unsigned> {
    friend dfa_builder;

    bool _is_compact;

    template<enum product_action product_action>
    friend class dfa_product_builder;
public:
    typedef transition_t<unsigned> transition;
    typedef std::vector<std::vector<transition>> transitions;

    nfa get_nfa() const;
    dfa disjunct(const dfa& other) const;
    dfa intersect(const dfa& other) const;
    dfa complement() const;
    dfa compact() const;

    zstring get_string() const;

    bool is_compact() const { return _is_compact; }

    bool is_empty() const {
        SASSERT(is_compact());
        return _accept_states.empty();
    }

    dfa();

    std::ostream& pp(std::ostream& out) const;
private:
#ifdef Z3DEBUG
    bool check_invariant() const;
#endif // def Z3DEBUG

    dfa(unsigned start_state,
        const std::set<unsigned>& accept_states,
        const transitions& transitions,
        bool is_compact = false);

    static const dfa empty;
};

class nfa: public automaton<std::vector<unsigned>> {
    friend dfa_builder;
    friend dfa;

public:
    typedef transition_t<std::vector<unsigned>> transition;
    typedef std::vector<std::vector<transition>> transitions;

    struct transition_greater_than_obj {
        bool operator()(const nfa::transition& a, const nfa::transition& b);
    };

    nfa();

private:
    nfa(unsigned start_state,
        const std::set<unsigned>& accept_states,
        const transitions& transitions);

#ifdef Z3DEBUG
    bool check_invariant() const;
#endif // def Z3DEBUG

    static transition make_epsilon_transition(unsigned tgt);
    static void add_transition(transitions* transitions, unsigned from, const transition& transition);
    static transition shift_transition(const transition& t, unsigned by);
    static std::vector<transition> shift_transitions(const std::vector<transition>& ts, unsigned by);

    transitions shift_states(unsigned by) const;

    std::set<unsigned> epsilon_closure(const std::vector<unsigned>& from_state) const;

public:
    static transitions normalize_transitions_map(const transitions& transitions);
    static bool transition_greater_than(const transition& a, const transition& b);
    static bool transition_less_than(const transition& a, const transition& b);

    dfa get_dfa() const;

    static nfa all();
    static nfa all_char();

    static const nfa empty;

    static nfa from_range(unsigned begin, unsigned end, ast_manager& m);
    static nfa from_string(const zstring& s);

    nfa append(const nfa& other) const;
    nfa disjunct(const nfa& other) const;
    nfa opt() const;
    nfa plus() const;
    nfa star() const;

    std::ostream& pp(std::ostream& out) const;
};

} /* namespace automata */

class theory_automata : public theory {

    automata::dfa get_dfa(expr* e);
    automata::nfa get_nfa(expr* e);

protected:
    final_check_status final_check_eh() override;
    bool internalize_atom(app*, bool) override;
    bool internalize_term(app*) override;
    void internalize_eq_eh(app * atom, bool_var v) override;
    void apply_sort_cnstr(enode* n, sort* s) override;
    void assign_eh(bool_var v, bool is_true) override;
    void new_eq_eh(theory_var, theory_var) override;
    bool use_diseqs() const override { return true; }
    void new_diseq_eh(theory_var, theory_var) override;
    void relevant_eh(app* n) override;
    void restart_eh() override;
    void push_scope_eh() override;
    void pop_scope_eh(unsigned num_scopes) override;
    void add_theory_assumptions(expr_ref_vector & assumptions) override;
    void init_search_eh() override;
    void propagate() override;
    theory* mk_fresh(context* new_ctx) override { return alloc(theory_automata, new_ctx->get_manager()); }
    char const* get_name() const override { return "automata"; }
    void display(std::ostream& out) const override {}
    model_value_proc* mk_value(enode* n, model_generator& mg) override;

public:
    theory_automata(ast_manager& m);
    virtual ~theory_automata();
    void init_model(model_generator & mg) override;

    trail_stack<theory_automata>& get_trail_stack() { return m_trail_stack; }

private:
    void string_must_be_in(expr* string, expr* pattern, literal l);
    void ensure_entry_for_var(expr* e);

    ast_manager& m;
    trail_stack<theory_automata> m_trail_stack;
    seq_util m_util;
    obj_map<expr, scoped_vector<std::pair<literal, automata::dfa>>> m_automata_per_var;
    obj_map<expr, automata::dfa> m_dfa_cache;
    obj_map<expr, automata::nfa> m_nfa_cache;

    theory_var mk_var(enode* n) override;
    enode* ensure_enode(expr* e);
};

}; /* namespace smt */

#endif /* THEORY_AUTOMATA_H_ */
