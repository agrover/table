// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

extern crate uuid;

use std::collections::HashMap;
use std::collections::hash_map;
use std::iter::IntoIterator;

use uuid::Uuid;

/// Map UUID and name to T items.
#[derive(Debug)]
pub struct Table<T> {
    name_to_uuid: HashMap<String, Uuid>,
    items: HashMap<Uuid, T>,
}

impl<T> Default for Table<T> {
    fn default() -> Table<T> {
        Table {
            name_to_uuid: HashMap::default(),
            items: HashMap::default(),
        }
    }
}

impl<'a, T> IntoIterator for &'a mut Table<T> {
    type Item = (&'a Uuid, &'a mut T);
    type IntoIter = hash_map::IterMut<'a, Uuid, T>;

    fn into_iter(self) -> hash_map::IterMut<'a, Uuid, T> {
        self.items.iter_mut()
    }
}

impl<'a, T> IntoIterator for &'a Table<T> {
    type Item = (&'a Uuid, &'a T);
    type IntoIter = hash_map::Iter<'a, Uuid, T>;

    fn into_iter(self) -> hash_map::Iter<'a, Uuid, T> {
        self.items.iter()
    }
}

pub struct Iter<'a, T: 'a> {
    name_iter: hash_map::Iter<'a, String, Uuid>,
    items: &'a HashMap<Uuid, T>,
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = (&'a str, &'a Uuid, &'a T);

    #[inline]
    fn next(&mut self) -> Option<(&'a str, &'a Uuid, &'a T)> {
        self.name_iter
            .next()
            .and_then(|(name, uuid)| self.items.get(&uuid).map(|item| (&**name, uuid, item)))
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.name_iter.size_hint()
    }
}

pub struct IterMut<'a, T: 'a> {
    name_iter: hash_map::Iter<'a, String, Uuid>,
    items: &'a mut HashMap<Uuid, T>,
}

impl<'a, T> Iterator for IterMut<'a, T> {
    type Item = (&'a str, &'a Uuid, &'a mut T);

    #[inline]
    fn next(&mut self) -> Option<(&'a str, &'a Uuid, &'a mut T)> {
        self.name_iter
            .next()
            .and_then(|(name, uuid)| {
                          self.items
                              .get_mut(&uuid)
                              .map(|item| (&**name, uuid, item))
                      })
    }
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.name_iter.size_hint()
    }
}

/// All operations are O(1).
/// The implementation does not priviledge the name key over the UUID key
/// in any way. They are both treated as constants once the item has been
/// inserted. In order to rename a T item, it must be removed, renamed, and
/// reinserted under the new name.
impl<T> Table<T> {
    /// Empty this table of all its items, returning them in a vector.
    pub fn empty(self) -> HashMap<Uuid, T> {
        self.items
    }

    pub fn is_empty(&self) -> bool {
        self.items.is_empty()
    }

    pub fn len(&self) -> usize {
        self.items.len()
    }

    pub fn iter(&self) -> Iter<T> {
        Iter {
            name_iter: self.name_to_uuid.iter(),
            items: &self.items,
        }
    }

    pub fn iter_mut(&mut self) -> IterMut<T> {
        IterMut {
            name_iter: self.name_to_uuid.iter(),
            items: &mut self.items,
        }
    }

    /// Returns true if map has an item corresponding to this name, else false.
    pub fn contains_name(&self, name: &str) -> bool {
        self.name_to_uuid.contains_key(name)
    }

    /// Returns true if map has an item corresponding to this uuid, else false.
    pub fn contains_uuid(&self, uuid: Uuid) -> bool {
        self.items.contains_key(&uuid)
    }

    /// Get item by name.
    pub fn get_by_name(&self, name: &str) -> Option<&T> {
        self.name_to_uuid
            .get(name)
            .and_then(|uuid| self.items.get(uuid))
    }

    /// Get item by uuid.
    pub fn get_by_uuid(&self, uuid: Uuid) -> Option<&T> {
        self.items.get(&uuid)
    }

    /// Get mutable item by name.
    pub fn get_mut_by_name(&mut self, name: &str) -> Option<&mut T> {
        if let Some(uuid) = self.name_to_uuid.get(name) {
            self.items.get_mut(uuid)
        } else {
            None
        }
    }

    /// Get mutable item by uuid.
    pub fn get_mut_by_uuid(&mut self, uuid: Uuid) -> Option<&mut T> {
        self.items.get_mut(&uuid)
    }

    /// Removes the item corresponding to name if there is one.
    pub fn remove_by_name(&mut self, name: &str) -> Option<T> {
        if let Some(uuid) = self.name_to_uuid.remove(name) {
            self.items.remove(&uuid)
        } else {
            None
        }
    }

    /// Removes the item corresponding to the uuid if there is one.
    pub fn remove_by_uuid(&mut self, uuid: Uuid) -> Option<(String, T)> {
        if let Some(item) = self.items.remove(&uuid) {
            let name = self.name_to_uuid
                .iter()
                .find(|&(_, item_uuid)| *item_uuid == uuid)
                .expect("should be there")
                .0
                .to_owned();
            self.name_to_uuid.remove(&name);
            Some((name, item))
        } else {
            None
        }
    }

    /// Inserts an item for given uuid and name.
    /// Possibly returns the item displaced.
    pub fn insert(&mut self, name: String, uuid: Uuid, item: T) -> Option<(String, Uuid, T)> {
        let old_uuid = self.name_to_uuid.insert(name.clone(), uuid);
        if let Some(old_uuid) = old_uuid {
            // (existing name, new uuid) OR (existing name, existing uuid)
            self.items.insert(uuid, item);
            if let Some(old_item) = self.items.remove(&old_uuid) {
                return Some((name, old_uuid, old_item));
            }
        } else {
            // (new name, new uuid) OR (new name, existing uuid)
            if let Some(old_item) = self.items.insert(uuid, item) {
                let old_name = self.name_to_uuid
                    .iter()
                    .find(|&(k, v)| *v == uuid && *k != name)
                    .expect("should be there")
                    .0
                    .to_owned();
                self.name_to_uuid.remove(&old_name);
                return Some((old_name, uuid, old_item));
            }
        }
        None
    }
}

#[cfg(test)]
mod tests {

    use rand;
    use uuid::Uuid;

    use super::Table;

    #[derive(Debug)]
    struct TestThing {
        name: String,
        uuid: Uuid,
        stuff: u32,
    }

    // A global invariant checker for the table.
    // Verifies proper relationship between internal data structures.
    fn table_invariant<T>(table: &Table<T>) -> () {
        for (uuid, item) in &table.items {
            // assert_eq!(*uuid, *table.name_to_uuid.get(item.name()).unwrap())
        }

        // No extra garbage
        assert_eq!(table.name_to_uuid.len(), table.items.len())
    }

    impl TestThing {
        pub fn new(name: &str, uuid: Uuid) -> TestThing {
            TestThing {
                name: name.to_owned(),
                uuid: uuid.clone(),
                stuff: rand::random::<u32>(),
            }
        }
    }

    #[test]
    /// Remove a test object by its uuid.
    /// Mutate the removed test object.
    /// Verify that the table is now empty and that removing by name yields
    /// no result.
    fn remove_existing_item() {
        let mut t: Table<TestThing> = Table::default();
        table_invariant(&t);

        let uuid = Uuid::new_v4();
        let name = "name";
        t.insert(name.to_owned(), uuid, TestThing::new(&name, uuid));
        table_invariant(&t);

        assert!(t.get_by_name(&name).is_some());
        assert!(t.get_by_uuid(uuid).is_some());
        let thing = t.remove_by_uuid(uuid);
        table_invariant(&t);
        assert!(thing.is_some());
        let mut thing = thing.unwrap();
        thing.1.stuff = 0;
        assert!(t.is_empty());
        assert!(t.remove_by_name(&name).is_none());
        table_invariant(&t);

        assert!(t.get_by_name(&name).is_none());
        assert!(t.get_by_uuid(uuid).is_none());
    }

    #[test]
    /// Insert a thing and then insert another thing with same keys.
    /// The previously inserted thing should be returned.
    /// You can't insert the identical thing, because that would be a move.
    /// This is good, because then you can't have a thing that is both in
    /// the table and not in the table.
    fn insert_same_keys() {
        let mut t: Table<TestThing> = Table::default();
        table_invariant(&t);

        let uuid = Uuid::new_v4();
        let name = "name";
        let thing = TestThing::new(&name, uuid);
        let thing_key = thing.stuff;
        let displaced = t.insert(name.to_owned(), uuid, thing);
        table_invariant(&t);

        // There was nothing previously, so displaced must be empty.
        assert!(displaced.is_none());

        // t now contains the inserted thing.
        assert!(t.contains_name(&name));
        assert!(t.contains_uuid(uuid));
        assert!(t.get_by_uuid(uuid).unwrap().stuff == thing_key);

        // Add another thing with the same keys.
        let thing2 = TestThing::new(&name, uuid);
        let thing_key2 = thing2.stuff;
        let displaced = t.insert(name.to_owned(), uuid, thing2);
        table_invariant(&t);

        // It has displaced the old thing.
        assert!(displaced.is_some());
        let ref displaced_item = displaced.unwrap();
        assert!(displaced_item.0 == name);
        assert!(displaced_item.1 == uuid);

        // But it contains a thing with the same keys.
        assert!(t.contains_name(&name));
        assert!(t.contains_uuid(uuid));
        assert!(t.get_by_uuid(uuid).unwrap().stuff == thing_key2);
        assert!(t.len() == 1);
    }

    #[test]
    /// Insert a thing and then insert another thing with the same name.
    /// The previously inserted thing should be returned.
    fn insert_same_name() {
        let mut t: Table<TestThing> = Table::default();
        table_invariant(&t);

        let uuid = Uuid::new_v4();
        let name = "name";
        let thing = TestThing::new(&name, uuid);
        let thing_key = thing.stuff;

        // There was nothing in the table before, so displaced is empty.
        let displaced = t.insert(name.to_owned(), uuid, thing);
        table_invariant(&t);
        assert!(displaced.is_none());

        // t now contains thing.
        assert!(t.contains_name(&name));
        assert!(t.contains_uuid(uuid));

        // Insert new item with different UUID.
        let uuid2 = Uuid::new_v4();
        let thing2 = TestThing::new(&name, uuid2);
        let thing_key2 = thing2.stuff;
        let displaced = t.insert(name.to_owned(), uuid2, thing2);
        table_invariant(&t);

        // The items displaced consist exactly of the first item.
        assert!(displaced.is_some());
        let ref displaced_item = displaced.unwrap();
        assert!(displaced_item.0 == name);
        assert!(displaced_item.1 == uuid);
        assert!(displaced_item.2.stuff == thing_key);

        // The table contains the new item and has no memory of the old.
        assert!(t.contains_name(&name));
        assert!(t.contains_uuid(uuid2));
        assert!(!t.contains_uuid(uuid));
        assert!(t.get_by_uuid(uuid2).unwrap().stuff == thing_key2);
        assert!(t.get_by_name(&name).unwrap().stuff == thing_key2);
        assert!(t.len() == 1);
    }

    #[test]
    /// Insert a thing and then insert another thing with the same uuid.
    /// The previously inserted thing should be returned.
    fn insert_same_uuid() {
        let mut t: Table<TestThing> = Table::default();
        table_invariant(&t);

        let uuid = Uuid::new_v4();
        let name = "name";
        let thing = TestThing::new(&name, uuid);
        let thing_key = thing.stuff;

        // There was nothing in the table before, so displaced is empty.
        let displaced = t.insert(name.to_owned(), uuid, thing);
        table_invariant(&t);
        assert!(displaced.is_none());

        // t now contains thing.
        assert!(t.contains_name(&name));
        assert!(t.contains_uuid(uuid));

        // Insert new item with different UUID.
        let name2 = "name2";
        let thing2 = TestThing::new(&name2, uuid);
        let thing_key2 = thing2.stuff;
        let displaced = t.insert(name2.to_owned(), uuid, thing2);
        table_invariant(&t);

        // The items displaced consist exactly of the first item.
        assert!(displaced.is_some());
        let ref displaced_item = displaced.unwrap();
        assert!(displaced_item.0 == name);
        assert!(displaced_item.1 == uuid);
        assert!(displaced_item.2.stuff == thing_key);

        // The table contains the new item and has no memory of the old.
        assert!(t.contains_uuid(uuid));
        assert!(t.contains_name(name2));
        assert!(!t.contains_name(name));
        assert!(t.get_by_uuid(uuid).unwrap().stuff == thing_key2);
        assert!(t.get_by_name(&name2).unwrap().stuff == thing_key2);
        assert!(t.len() == 1);
    }
}
