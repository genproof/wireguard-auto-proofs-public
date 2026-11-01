/* shimtest only (native, not verified): the kernel list/hash-table primitives that upstream peerlookup.c uses,
 * with the bodies of include/linux/list.h, rculist.h, hashtable.h and types.h at the pinned commit (RCU
 * accessors as plain accesses, single-threaded). */
#ifndef SHIMTEST_HASHTABLE_H
#define SHIMTEST_HASHTABLE_H
#include "quickproof_kernel.h"

struct hlist_head { struct hlist_node *first; };
struct hlist_node { struct hlist_node *next, **pprev; };

#define DECLARE_HASHTABLE(name, bits) struct hlist_head name[1 << (bits)]
#define HASH_SIZE(name) (ARRAY_SIZE(name))
#define hash_init(ht) do { for (size_t _i = 0; _i < HASH_SIZE(ht); _i++) (ht)[_i].first = NULL; } while (0)
#define LIST_POISON2 ((void *)0x122)

static inline void INIT_HLIST_NODE(struct hlist_node *h) { h->next = NULL; h->pprev = NULL; }
static inline int hlist_unhashed(const struct hlist_node *h) { return !h->pprev; }
static inline void __hlist_del(struct hlist_node *n)
{
	struct hlist_node *next = n->next;
	struct hlist_node **pprev = n->pprev;
	*pprev = next;
	if (next)
		next->pprev = pprev;
}
static inline void hlist_del_init_rcu(struct hlist_node *n)
{
	if (!hlist_unhashed(n)) {
		__hlist_del(n);
		n->pprev = NULL;
	}
}
static inline void hlist_replace_rcu(struct hlist_node *old, struct hlist_node *new)
{
	struct hlist_node *next = old->next;
	new->next = next;
	new->pprev = old->pprev;
	*new->pprev = new;
	if (next)
		new->next->pprev = &new->next;
	old->pprev = LIST_POISON2;
}
static inline void hlist_add_head_rcu(struct hlist_node *n, struct hlist_head *h)
{
	struct hlist_node *first = h->first;
	n->next = first;
	n->pprev = &h->first;
	h->first = n;
	if (first)
		first->pprev = &n->next;
}
#define hlist_entry_safe(ptr, type, member) \
	({ typeof(ptr) ____ptr = (ptr); ____ptr ? container_of(____ptr, type, member) : NULL; })
#define hlist_for_each_entry_rcu_bh(pos, head, member) \
	for (pos = hlist_entry_safe((head)->first, typeof(*(pos)), member); pos; \
	     pos = hlist_entry_safe((pos)->member.next, typeof(*(pos)), member))

#define mutex_init(m) ((void)0)
#define mutex_lock(m) ((void)0)
#define mutex_unlock(m) ((void)0)
#define kvmalloc_obj(x) calloc(1, sizeof(x))
#endif
