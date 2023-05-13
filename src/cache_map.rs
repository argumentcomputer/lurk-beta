use stable_deref_trait::StableDeref;
use std::borrow::Borrow;
use std::collections::HashMap;
use std::hash::Hash;

use std::sync::RwLock;

#[derive(Debug)]
/// `CacheMap` is an adaptation of `FrozenMap`:
/// `<https://docs.rs/elsa/latest/elsa/map/struct.FrozenMap.html>`
pub struct CacheMap<K, V> {
    map: RwLock<HashMap<K, V, ahash::RandomState>>,
}

impl<K, V> Default for CacheMap<K, V> {
    fn default() -> Self {
        Self {
            map: Default::default(),
        }
    }
}

impl<K, V> CacheMap<K, V> {
    pub fn new() -> Self {
        Self::default()
    }
}

impl<K: Eq + Hash, V: StableDeref> CacheMap<K, V> {
    // these should never return &K or &V
    // these should never delete any entries

    /// If the key exists in the map, returns a reference
    /// to the corresponding value, otherwise inserts a
    /// new entry in the map for that key and returns a
    /// reference to the given value.
    ///
    /// Existing values are never overwritten.
    ///
    /// The key may be any borrowed form of the map's key type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// use elsa::sync::CacheMap;
    ///
    /// let map = CacheMap::new();
    /// assert_eq!(map.insert(1, Box::new("a")), &"a");
    /// assert_eq!(map.insert(1, Box::new("b")), &"a");
    /// ```
    pub fn insert(&self, k: K, v: V) -> &V::Target {
        let mut map = self.map.write().unwrap();
        let ret = unsafe {
            let inserted = &**map.entry(k).or_insert(v);
            &*(inserted as *const _)
        };
        ret
    }

    /// If the key exists in the map, returns a reference to the corresponding
    /// value, otherwise inserts a new entry in the map for that key and the
    /// value returned by the creation function, and returns a reference to the
    /// generated value.
    ///
    /// Existing values are never overwritten.
    ///
    /// The key may be any borrowed form of the map's key type, but [`Hash`] and
    /// [`Eq`] on the borrowed form *must* match those for the key type.
    ///
    /// **Note** that the write lock is held for the duration of this function’s
    /// execution, even while the value creation function is executing (if
    /// needed). This will block any concurrent `get` or `insert` calls.
    ///
    /// # Examples
    ///
    /// ```
    /// use elsa::sync::CacheMap;
    ///
    /// let map = CacheMap::new();
    /// assert_eq!(map.insert_with(1, || Box::new("a")), &"a");
    /// assert_eq!(map.insert_with(1, || unreachable!()), &"a");
    /// ```
    pub fn insert_with(&self, k: K, f: impl FnOnce() -> V) -> &V::Target {
        let mut map = self.map.write().unwrap();
        let ret = unsafe {
            let inserted = &**map.entry(k).or_insert_with(f);
            &*(inserted as *const _)
        };
        ret
    }

    /// If the key exists in the map, returns a reference to the corresponding
    /// value, otherwise inserts a new entry in the map for that key and the
    /// value returned by the creation function, and returns a reference to the
    /// generated value.
    ///
    /// Existing values are never overwritten.
    ///
    /// The key may be any borrowed form of the map's key type, but [`Hash`] and
    /// [`Eq`] on the borrowed form *must* match those for the key type.
    ///
    /// **Note** that the write lock is held for the duration of this function’s
    /// execution, even while the value creation function is executing (if
    /// needed). This will block any concurrent `get` or `insert` calls.
    ///
    /// # Examples
    ///
    /// ```
    /// use elsa::sync::CacheMap;
    ///
    /// let map = CacheMap::new();
    /// assert_eq!(map.insert_with_key(1, |_| Box::new("a")), &"a");
    /// assert_eq!(map.insert_with_key(1, |_| unreachable!()), &"a");
    /// ```
    pub fn insert_with_key(&self, k: K, f: impl FnOnce(&K) -> V) -> &V::Target {
        let mut map = self.map.write().unwrap();
        let ret = unsafe {
            let inserted = &**map.entry(k).or_insert_with_key(f);
            &*(inserted as *const _)
        };
        ret
    }

    /// Returns a reference to the value corresponding to the key.
    ///
    /// The key may be any borrowed form of the map's key type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// use elsa::sync::CacheMap;
    ///
    /// let map = CacheMap::new();
    /// map.insert(1, Box::new("a"));
    /// assert_eq!(map.get(&1), Some(&"a"));
    /// assert_eq!(map.get(&2), None);
    /// ```
    pub fn get<Q: ?Sized>(&self, k: &Q) -> Option<&V::Target>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        let map = self.map.read().unwrap();
        let ret = unsafe { map.get(k).map(|x| &*(&**x as *const V::Target)) };
        ret
    }

    /// Applies a function to the owner of the value corresponding to the key (if any).
    ///
    /// The key may be any borrowed form of the map's key type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// use elsa::sync::CacheMap;
    ///
    /// let map = CacheMap::new();
    /// map.insert(1, Box::new("a"));
    /// assert_eq!(map.map_get(&1, Clone::clone), Some(Box::new("a")));
    /// assert_eq!(map.map_get(&2, Clone::clone), None);
    /// ```
    pub fn map_get<Q: ?Sized, T, F>(&self, k: &Q, f: F) -> Option<T>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
        F: FnOnce(&V) -> T,
    {
        let map = self.map.read().unwrap();
        let ret = map.get(k).map(f);
        ret
    }

    /// # Examples
    ///
    /// ```
    /// use elsa::sync::CacheMap;
    ///
    /// let map = CacheMap::new();
    /// assert_eq!(map.len(), 0);
    /// map.insert(1, Box::new("a"));
    /// assert_eq!(map.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        let map = self.map.read().unwrap();
        map.len()
    }

    /// # Examples
    ///
    /// ```
    /// use elsa::sync::CacheMap;
    ///
    /// let map = CacheMap::new();
    /// assert_eq!(map.is_empty(), true);
    /// map.insert(1, Box::new("a"));
    /// assert_eq!(map.is_empty(), false);
    /// ```
    pub fn is_empty(&self) -> bool {
        let map = self.map.read().unwrap();
        map.is_empty()
    }

    // TODO add more
}

impl<K: Clone, V> CacheMap<K, V> {
    pub fn keys_cloned(&self) -> Vec<K> {
        self.map.read().unwrap().keys().cloned().collect()
    }
}

impl<K: Eq + Hash, V: Copy> CacheMap<K, V> {
    /// Returns a copy of the value corresponding to the key.
    ///
    /// The key may be any borrowed form of the map's key type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// use elsa::sync::CacheMap;
    ///
    /// let map = CacheMap::new();
    /// map.get_copy_or_insert(1, 6);
    /// assert_eq!(map.get_copy(&1), Some(6));
    /// assert_eq!(map.get_copy(&2), None);
    /// ```
    pub fn get_copy<Q: ?Sized>(&self, k: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        let map = self.map.read().unwrap();
        map.get(k).cloned()
    }

    /// If the key exists in the map, returns a reference
    /// to the corresponding value, otherwise inserts a
    /// new entry in the map for that key and returns a
    /// reference to the given value.
    ///
    /// Existing values are never overwritten.
    ///
    /// The key may be any borrowed form of the map's key type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// use elsa::sync::CacheMap;
    ///
    /// let map = CacheMap::new();
    /// assert_eq!(map.get_copy_or_insert(1, 6), 6);
    /// assert_eq!(map.get_copy_or_insert(1, 12), 6);
    /// ```
    pub fn get_copy_or_insert(&self, k: K, v: V) -> V {
        let mut map = self.map.write().unwrap();
        // This is safe because `or_insert` does not overwrite existing values
        let inserted = map.entry(k).or_insert(v);
        *inserted
    }

    /// If the key exists in the map, returns a reference to the corresponding
    /// value, otherwise inserts a new entry in the map for that key and the
    /// value returned by the creation function, and returns a reference to the
    /// generated value.
    ///
    /// Existing values are never overwritten.
    ///
    /// The key may be any borrowed form of the map's key type, but [`Hash`] and
    /// [`Eq`] on the borrowed form *must* match those for the key type.
    ///
    /// **Note** that the write lock is held for the duration of this function’s
    /// execution, even while the value creation function is executing (if
    /// needed). This will block any concurrent `get` or `insert` calls.
    ///
    /// # Examples
    ///
    /// ```
    /// use elsa::sync::CacheMap;
    ///
    /// let map = CacheMap::new();
    /// assert_eq!(map.get_copy_or_insert_with(1, || 6), 6);
    /// assert_eq!(map.get_copy_or_insert_with(1, || unreachable!()), 6);
    /// ```
    pub fn get_copy_or_insert_with(&self, k: K, f: impl FnOnce() -> V) -> V {
        let mut map = self.map.write().unwrap();
        // This is safe because `or_insert_with` does not overwrite existing values
        let inserted = map.entry(k).or_insert_with(f);
        *inserted
    }

    /// If the key exists in the map, returns a reference to the corresponding
    /// value, otherwise inserts a new entry in the map for that key and the
    /// value returned by the creation function, and returns a reference to the
    /// generated value.
    ///
    /// Existing values are never overwritten.
    ///
    /// The key may be any borrowed form of the map's key type, but [`Hash`] and
    /// [`Eq`] on the borrowed form *must* match those for the key type.
    ///
    /// **Note** that the write lock is held for the duration of this function’s
    /// execution, even while the value creation function is executing (if
    /// needed). This will block any concurrent `get` or `insert` calls.
    ///
    /// # Examples
    ///
    /// ```
    /// use elsa::sync::CacheMap;
    ///
    /// let map = CacheMap::new();
    /// assert_eq!(map.get_copy_or_insert_with_key(1, |_| 6), 6);
    /// assert_eq!(map.get_copy_or_insert_with_key(1, |_| unreachable!()), 6);
    /// ```
    pub fn get_copy_or_insert_with_key(&self, k: K, f: impl FnOnce(&K) -> V) -> V {
        let mut map = self.map.write().unwrap();
        // This is safe because `or_insert_with_key` does not overwrite existing values
        let inserted = map.entry(k).or_insert_with_key(f);
        *inserted
    }
}

impl<K, V> std::convert::AsMut<HashMap<K, V, ahash::RandomState>> for CacheMap<K, V> {
    /// Get mutable access to the underlying [`HashMap`].
    ///
    /// This is safe, as it requires a `&mut self`, ensuring nothing is using
    /// the 'frozen' contents.
    fn as_mut(&mut self) -> &mut HashMap<K, V, ahash::RandomState> {
        self.map.get_mut().unwrap()
    }
}
