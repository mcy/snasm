//! Debug information attached to an object file, describing the assembly file
//! it was assembled from.

use std::collections::BTreeMap;
use std::path::PathBuf;

use serde::Deserialize;
use serde::Serialize;

use crate::int::u24;

/// Overall metadata for a a ROM, as a collection of [`File`]s.
///
/// [`File`]: struct.File.html
#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct Metadata {
  /// A list of assembly files that a ROM was assembled from.
  pub files: Vec<File>,
}

/// Non-program information associated with an [`Object`], which describes the
/// assembly file it came from.
#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct File {
  /// The name of the original assembly file.
  pub name: PathBuf,
  /// Blocks within the original obct file.
  pub blocks: Vec<Block>,
}

/// A [`Block`] which now only carries it associated metadata, describing where
/// to find its code relative to some ROM.
///
/// [`Block`]: ../struct.Block.html
#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct Block {
  /// The start of this `Block` as an absolute address.
  pub start: u24,
  /// The length of this `Block`.
  pub len: u16,
  /// `Offset` information within the block.
  #[serde(default)]
  #[serde(skip_serializing_if = "Vec::is_empty")]
  pub offsets: Vec<Offset>,
  /// Labels defined within this block.
  #[serde(default)]
  #[serde(skip_serializing_if = "BTreeMap::is_empty")]
  #[serde(with = "kv_pairs")]
  pub labels: BTreeMap<u16, Label>,
}

/// A program label within a [`Block`].
///
/// [`Block`]: ../struct.Block.html
#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(untagged)]
pub enum Label {
  /// A symbolic label.
  Symbol(Symbol),
  /// A local digit label.
  Local(u8),
}

/// A debugging symbol.
#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct Symbol {
  /// The symbol's name.
  pub name: String,
  /// Whether this symbol was a global symbol.
  #[serde(default)]
  #[serde(skip_serializing_if = "is_false")]
  pub is_global: bool,
}

fn is_false(b: &bool) -> bool {
  *b == false
}

/// An "offset" within a [`Block`], describing whether it contains code or some
/// kind of data.
///
/// [`Block`]: ../struct.Block.html
#[derive(Copy, Clone, PartialEq, Eq, Debug, Deserialize, Serialize)]
pub struct Offset {
  /// The data offset that this `Offset` begins at.
  pub start: u16,
  /// The length of this `Offset`.
  pub len: u16,
  /// The type of this `Offset`.
  pub ty: OffsetType,
}

/// A type of [`Offset`], indicating whether it was declared as code or data.
///
/// [`Offset`]: ../struct.Offset.html
#[derive(Copy, Clone, PartialEq, Eq, Debug, Deserialize, Serialize)]
pub enum OffsetType {
  /// Indicates an offset that was defined as processor instructions.
  Code,
  /// Indicates an offset that was defined as data.
  Data,
}

/// Serde serializer/deserializer for (de)serializing a map as a sequence of
/// key-value pairs.
mod kv_pairs {
  use std::fmt;
  use std::marker::PhantomData;

  use serde::de;
  use serde::Deserialize;
  use serde::Deserializer;
  use serde::Serialize;
  use serde::Serializer;

  pub fn serialize<K, V, Map, S>(map: Map, ser: S) -> Result<S::Ok, S::Error>
  where
    K: Serialize,
    V: Serialize,
    Map: IntoIterator<Item = (K, V)>,
    S: Serializer,
  {
    ser.collect_seq(map)
  }

  pub fn deserialize<'de, K, V, Map, D>(de: D) -> Result<Map, D::Error>
  where
    K: Deserialize<'de>,
    V: Deserialize<'de>,
    Map: Default + Extend<(K, V)>,
    D: Deserializer<'de>,
  {
    struct MapVisitor<K, V, Map>(PhantomData<(K, V, Map)>);
    impl<'de, K, V, Map> de::Visitor<'de> for MapVisitor<K, V, Map>
    where
      K: Deserialize<'de>,
      V: Deserialize<'de>,
      Map: Default + Extend<(K, V)>,
    {
      type Value = Map;

      fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("a sequence of key-value pairs")
      }

      fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
      where
        A: de::SeqAccess<'de>,
      {
        let mut map = Map::default();
        while let Some((k, v)) = seq.next_element()? {
          map.extend(Some((k, v)));
        }
        Ok(map)
      }
    }

    de.deserialize_seq(MapVisitor(PhantomData))
  }
}
