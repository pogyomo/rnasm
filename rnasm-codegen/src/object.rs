use derive_new::new;

macro_rules! impl_convert {
    ($target:ident, $($source:ident),*) => {$(
        impl From<$source> for $target {
            fn from(source: $source) -> $target {
                $target::$source(source)
            }
        }
    )*};
}

impl_convert!(Object, IntegerObj, StringObj);

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Object {
    IntegerObj(IntegerObj),
    StringObj(StringObj),
}

#[derive(new)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct IntegerObj {
    pub value: u16,
}

#[derive(new)]
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct StringObj {
    pub value: String,
}
