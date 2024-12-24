//! A sparse, HashMap based, 2d grid.
//!
//! Feel free to request more utilities and suggest improvements.
//! Even better, make a PR <3, and reward yourself with some delicious flammkuchen (you can include a picture in the PR if you want <3).
//!
//! Happy {holi}days!

use std::collections::HashMap;

/// Sparse 2d grid. A thin wrapper around the famous HashMap. Packed
/// and backed by (useful?) utilities.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct SparseGrid<V> {
    inner: HashMap<Point, V>,
}

impl<V> SparseGrid<V> {
    pub fn new() -> Self {
        Self {
            inner: HashMap::new(),
        }
    }

    pub fn get(&self, point: &Point) -> Option<&V> {
        self.inner.get(point)
    }

    pub fn insert(&mut self, point: Point, value: V) {
        self.inner.insert(point, value);
    }
}

impl<V: Default> SparseGrid<V> {
    pub fn from_iter_with_default<T: IntoIterator<Item = Point>>(iter: T) -> Self {
        iter.into_iter()
            .fold(SparseGrid::default(), |mut acc, point| {
                acc.insert(point, Default::default());
                acc
            })
    }
}

impl<V> FromIterator<(Point, V)> for SparseGrid<V> {
    fn from_iter<T: IntoIterator<Item = (Point, V)>>(iter: T) -> Self {
        iter.into_iter()
            .fold(SparseGrid::new(), |mut acc, (point, value)| {
                acc.insert(point, value);
                acc
            })
    }
}

impl<V: Clone> SparseGrid<V> {
    pub fn from_iter_with_value<T: IntoIterator<Item = Point>>(iter: T, value: V) -> Self {
        iter.into_iter().fold(SparseGrid::new(), |mut acc, point| {
            acc.insert(point, value.clone());
            acc
        })
    }
}

impl<V: Clone> SparseGrid<V> {
    pub fn neighbors(&self, p: Point) -> Neighbors<V> {
        Neighbors {
            north: p
                .y
                .checked_sub(1)
                .and_then(|y| self.inner.get(&Point { x: p.x, y }))
                .cloned(),
            east: p
                .x
                .checked_add(1)
                .and_then(|x| self.inner.get(&Point { x, y: p.y }))
                .cloned(),
            south: p
                .y
                .checked_add(1)
                .and_then(|y| self.inner.get(&Point { x: p.x, y }))
                .cloned(),
            west: p
                .x
                .checked_sub(1)
                .and_then(|x| self.inner.get(&Point { x, y: p.y }))
                .cloned(),
        }
    }
}

#[derive(Copy, Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Point {
    pub x: i32,
    pub y: i32,
}

impl Point {
    pub fn new(x: i32, y: i32) -> Self {
        Self { x, y }
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Neighbors<V> {
    pub north: Option<V>,
    pub east: Option<V>,
    pub south: Option<V>,
    pub west: Option<V>,
}

impl<V> Neighbors<V> {
    /// In order: north, east, south, west
    pub fn as_array(&self) -> [Option<&V>; 4] {
        [
            self.north.as_ref(),
            self.east.as_ref(),
            self.south.as_ref(),
            self.west.as_ref(),
        ]
    }

    pub fn count(&self) -> usize {
        self.as_array().iter().flatten().count()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use yare::parameterized;

    #[parameterized(
        is_north = { vec![(Point { x: 0, y: 0 }, -1), (Point { x: 0, y: -1 }, 123)] },
        is_east = { vec![(Point { x: 0, y: 0 }, -1), (Point { x: 1, y: 0 }, 123)] },
        is_south = { vec![(Point { x: 0, y: 0 }, -1), (Point { x: 0, y: 1 }, 123)] },
        is_west = { vec![(Point { x: 0, y: 0 }, -1), (Point { x: -1, y: 0 }, 123)] },
    )]
    fn from_iter(input: Vec<(Point, i32)>) {
        let grid = SparseGrid::from_iter(input);
        let origin = Point { x: 0, y: 0 };

        assert_eq!(*grid.get(&origin).unwrap(), -1);

        let neighbors = grid.neighbors(origin);
        let n = neighbors.count();
        assert_eq!(n, 1);

        let array = neighbors.as_array();
        let mut iter = array.iter().flatten();

        assert_eq!(**iter.next().unwrap(), 123);
        assert_eq!(iter.next(), None);
    }

    #[parameterized(
        is_north = { vec![Point { x: 0, y: 0 }, Point { x: 0, y: -1 }] },
        is_east = { vec![Point { x: 0, y: 0 }, Point { x: 1, y: 0 }] },
        is_south = { vec![Point { x: 0, y: 0 }, Point { x: 0, y: 1 }] },
        is_west = { vec![Point { x: 0, y: 0 }, Point { x: -1, y: 0 }] },
    )]
    fn from_iter_with_default(input: Vec<Point>) {
        let grid = SparseGrid::<u8>::from_iter_with_default(input);
        let origin = Point { x: 0, y: 0 };

        assert_eq!(*grid.get(&origin).unwrap(), 0);

        let neighbors = grid.neighbors(origin);
        let n = neighbors.count();

        assert_eq!(n, 1);

        let array = neighbors.as_array();
        let mut iter = array.iter().flatten();

        assert_eq!(**iter.next().unwrap(), 0);
        assert_eq!(iter.next(), None);
    }

    #[parameterized(
        is_north = { vec![Point { x: 0, y: 0 }, Point { x: 0, y: -1 }] },
        is_east = { vec![Point { x: 0, y: 0 }, Point { x: 1, y: 0 }] },
        is_south = { vec![Point { x: 0, y: 0 }, Point { x: 0, y: 1 }] },
        is_west = { vec![Point { x: 0, y: 0 }, Point { x: -1, y: 0 }] },
    )]
    fn from_iter_with_value(input: Vec<Point>) {
        let grid = SparseGrid::<u8>::from_iter_with_value(input, 123);
        let origin = Point { x: 0, y: 0 };

        assert_eq!(*grid.get(&origin).unwrap(), 123);

        let neighbors = grid.neighbors(origin);
        let n = neighbors.count();

        assert_eq!(n, 1);

        let array = neighbors.as_array();
        let mut iter = array.iter().flatten();

        assert_eq!(**iter.next().unwrap(), 123);
        assert_eq!(iter.next(), None);
    }
}
