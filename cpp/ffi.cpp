#include <lean/lean.h>

struct Mutable {
    std::atomic<lean_object *> m_value;
    Mutable(lean_object * v) : m_value(v) { }
};

static void Mutable_finalize(void * o) {
    lean_dec(static_cast<Mutable *>(o)->m_value);
    delete static_cast<Mutable *>(o);
}

static void Mutable_foreach(void * o, b_lean_obj_arg f) {
    lean_inc(f);
    lean_apply_1(f, static_cast<Mutable *>(o)->m_value);
}

static lean_external_class * g_Mutable_class = nullptr;

static inline lean_object * Mutable_to_lean(Mutable * x) {
    if (g_Mutable_class == nullptr) {
        g_Mutable_class = lean_register_external_class(Mutable_finalize, Mutable_foreach);
    }
    return lean_alloc_external(g_Mutable_class, x);
}

static inline Mutable * lean_to_Mutable(b_lean_obj_arg o) {
    return static_cast<Mutable *>(lean_get_external_data(o));
}

extern "C" LEAN_EXPORT lean_obj_res lean_mk_Mutable(b_lean_obj_arg o) {
    return Mutable_to_lean(new Mutable(o));
}

extern "C" LEAN_EXPORT b_lean_obj_res lean_Mutable_get(b_lean_obj_arg x) {
    return lean_to_Mutable(x)->m_value;
}

extern "C" LEAN_EXPORT b_lean_obj_res lean_Mutable_modify(b_lean_obj_arg x, lean_obj_arg f) {
    lean_object * c = lean_to_Mutable(x)->m_value.exchange(nullptr);
    while (c == nullptr) {
        // std::this_thread::yield();
        c = lean_to_Mutable(x)->m_value.exchange(nullptr);
    }
    lean_object * r = lean_apply_1(f, c);
    // lean_assert(r != nullptr); /* Closure must return a valid lean object */
    // lean_assert(lean_to_Mutable(x)->m_value == nullptr);
    lean_inc(r);
    lean_to_Mutable(x)->m_value = r;
    return r;
}

extern "C" LEAN_EXPORT b_lean_obj_res lean_Mutable_modify2(b_lean_obj_arg x, lean_obj_arg f) {
    lean_object * c = lean_to_Mutable(x)->m_value.exchange(nullptr);
    while (c == nullptr) {
        // std::this_thread::yield();
        c = lean_to_Mutable(x)->m_value.exchange(nullptr);
    }
    lean_object * p = lean_apply_1(f, c);
    // lean_assert(p != nullptr); /* Closure must return a valid lean object */
    // lean_assert(lean_to_Mutable(x)->m_value == nullptr);
    lean_object * r = lean_ctor_get(p, 0); lean_inc(r);
    lean_object * n = lean_ctor_get(p, 1); lean_inc(n);
    lean_dec_ref(p);
    lean_to_Mutable(x)->m_value = n;
    return r;
}
