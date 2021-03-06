#ifndef MARPA_H
#define MARPA_H

extern "C" {
#include <marpa.h>
//#include <marpa_api.h>
}

extern const char* marpa_errors[92];
namespace marpa {

class value;

class grammar {
    public:
        typedef int earleme;
        typedef int error_code;
        typedef int symbol_id;
        typedef int rule_id;
        typedef int event_type;
        typedef int rank;

    private:
        typedef Marpa_Grammar handle_type;
    public:
        grammar() : handle(marpa_g_new(0)) {
            force_valued();
        }
        grammar(const grammar& g) {
            marpa_g_ref(g.handle);
            marpa_g_unref(this->handle);
            this->handle = g.handle;
        }

        grammar& operator=(const grammar& g) {
            marpa_g_ref(g.handle);
            marpa_g_unref(this->handle);
            this->handle = g.handle;
            return *this;
        }

        ~grammar() {
            marpa_g_unref(handle);
        }


        void force_valued() {
            marpa_g_force_valued(handle);
        }

        template <class T>
        void set_valued_rules(T& v) {
            for (auto r : rules) {
                v.rule_is_valued(r, 1);
            }
        }

        inline symbol_id start_symbol() const {
            return marpa_g_start_symbol(handle);
        }

        inline symbol_id start_symbol(symbol_id s) {
            return marpa_g_start_symbol_set(handle, s);
        }

        inline symbol_id new_symbol() {
            return marpa_g_symbol_new(handle);
        }

        inline rule_id new_rule(symbol_id lhs_id, symbol_id* rhs_ids, int length) {
            rule_id id = marpa_g_rule_new(handle, lhs_id, rhs_ids, length);
            rules.push_back(id);
            return id;
        }

        inline rule_id new_sequence(symbol_id lhs_id, symbol_id rhs_id, symbol_id separator_id, int min, int flags) {
            rule_id id = marpa_g_sequence_new(handle, lhs_id, rhs_id, separator_id, min, flags);
            rules.push_back(id);
            return id;
        }

        inline rule_id add_rule(symbol_id lhs_id, std::initializer_list<symbol_id> rhs) {
            grammar::symbol_id rhs_ids[rhs.size()]; 
            std::copy(rhs.begin(), rhs.end(), rhs_ids);
            return new_rule(lhs_id, rhs_ids, rhs.size());
        }

        inline rule_id add_sequence(symbol_id lhs_id, symbol_id rhs_id, symbol_id separator_id, int min, int flags) {
            return new_sequence(lhs_id, rhs_id, separator_id, min, flags);
        }

        inline
        rank rule_rank(rule_id rule) {
            return marpa_g_rule_rank(handle, rule);
        }

        inline
        rank rule_rank_set(rule_id rule, rank r) {
            return marpa_g_rule_rank_set(handle, rule, r);
        }

        inline void symbol_is_terminal(symbol_id sym_id, int value) {
            marpa_g_symbol_is_terminal_set(handle, sym_id, value);
        }

        inline int precompute() {
            return marpa_g_precompute(handle);
        }

        inline int error() {
            return marpa_g_error(handle, 0);
        }
    public:
        inline handle_type internal_handle() { return handle; }
    private:
        handle_type handle;
        std::vector<rule_id> rules;
};

class recognizer {
    private:
        typedef Marpa_Recognizer handle_type;

        handle_type handle;
    public:
        typedef int earley_set_id;

        inline handle_type internal_handle() {
            return handle;
        }
    public:
        recognizer(grammar& g)
            : handle(marpa_r_new(g.internal_handle())) {
            start_input();
        }

        ~recognizer() {
            marpa_r_unref(handle);
        }

        inline void start_input() {
            marpa_r_start_input(handle);
        }

        inline int alternative(grammar::symbol_id sym_id, int value, int length) {
            return marpa_r_alternative(handle, sym_id, value, length);
        }

        inline grammar::earleme earleme_complete() {
            return marpa_r_earleme_complete(handle);
        }

        inline earley_set_id latest_earley_set() {
            return marpa_r_latest_earley_set(handle);
        }

        int read(grammar::symbol_id sym_id, int value, int length, int line = -1) {
            if (value == 0) {
                //throw "value == 0";
                return 0;
            }
            int error = alternative(sym_id, value, length);
            if (error != MARPA_ERR_NONE) {
                std::cerr << "test2.toy:" << line << ": Error: " << marpa_errors[error] << "\n";
                return error;
            }
            return earleme_complete();
        }

        recognizer& operator=(const recognizer&) = delete;
        recognizer(const recognizer&) = delete;
    private:
};


class bocage {
    private:
        typedef Marpa_Bocage handle_type;
        handle_type handle;
    public:
        inline handle_type internal_handle() { return handle; }
    public:
        bocage(recognizer& r, recognizer::earley_set_id set_id) : handle(marpa_b_new(r.internal_handle(), set_id)) {}
        ~bocage() { if (handle) marpa_b_unref(handle); }

        bocage& operator=(const bocage&) = delete;
        bocage(const bocage&) = delete;
    private:
};

class order {
    private:
        typedef Marpa_Order handle_type;
        handle_type handle;
    public:
        inline handle_type internal_handle() { return handle; }
    public:
        order(bocage& b) : handle(marpa_o_new(b.internal_handle())) {}
        ~order() { marpa_o_unref(handle); }

        order& operator=(const order&) = delete;
        order(const order&) = delete;

        inline
        int high_rank_only() {
            return marpa_o_high_rank_only(handle);
        }

        inline
        void high_rank_only_set(int s) {
            marpa_o_high_rank_only_set(handle, s);
        }


        inline
        void rank() {
            marpa_o_rank(handle);
        }
    private:
};

class tree {
    private:
        typedef Marpa_Tree handle_type;
        handle_type handle;
    public:
        inline handle_type internal_handle() { return handle; }
    public:
        tree(order& o) : handle(marpa_t_new(o.internal_handle())) {}
        ~tree() { marpa_t_unref(handle); }

        inline int next() { return marpa_t_next(handle); }

        tree& operator=(const tree&) = delete;
        tree(const tree&) = delete;
    private:
};

class value {
    public:
        typedef int step_type;
    private:
        typedef Marpa_Value handle_type;

        handle_type handle;
    public:
        inline handle_type internal_handle() { return handle; }
    public:
        value(tree& t) : handle(marpa_v_new(t.internal_handle())) {}
        ~value() { marpa_v_unref(handle); }

        inline step_type step() { return marpa_v_step(handle); }
        inline void rule_is_valued(grammar::rule_id rule, int value) { marpa_v_rule_is_valued_set(handle, rule, value); }
        inline void symbol_is_valued(grammar::symbol_id rule, int value) { marpa_v_symbol_is_valued_set(handle, rule, value); }

        inline int result() { return marpa_v_result(handle); }
        inline int arg_0() { return marpa_v_arg_0(handle); }
        inline int arg_n() { return marpa_v_arg_n(handle); }
        inline int token_value() { return marpa_v_token_value(handle); }
        inline int rule() { return marpa_v_rule(handle); }
        inline grammar::symbol_id symbol() { return marpa_v_symbol(handle); }
        inline grammar::symbol_id token() { return marpa_v_token(handle); }

        value& operator=(const value&) = delete;
        value(const value&) = delete;

    private:
};

class event {
};

}

#endif
