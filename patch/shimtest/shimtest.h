#define NENT 24
#define NPEER 6
void t_init(void);
void t_entry(int e, int peer, int type);
void t_peer_key(int p, const u8 key[32]);
void t_peer_ref(int p, unsigned r);
unsigned t_peer_refs(int p);
void t_padd(int p);
int t_plookup(const u8 key[32]);
u32 t_insert(int e);
int t_replace(int o, int n);
void t_remove(int e);
int t_lookup(u32 index, int mask, int *peer);
int t_hashed(int e);
u32 t_index(int e);
int t_entry_peer(int e);
