//! Paths, files, the environment and the terminal: content-free specifications. The
//! file system and the environment are outside the program, so a result says nothing that
//! later calls could rely on; every operation that can fail may fail.
use super::super::prelude::*;
use std::ffi::{OsStr, OsString};
use std::path::{Path, PathBuf};

verus! {

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExPath(Path);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExPathBuf(PathBuf);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExOsStr(OsStr);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExOsString(OsString);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExPathDisplay<'a>(std::path::Display<'a>);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExFile(std::fs::File);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExReadDir(std::fs::ReadDir);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExDirEntry(std::fs::DirEntry);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExIoError(std::io::Error);

/// Transparent (a fieldless enum), so `ErrorKind::Other` etc. can be written.
#[verifier::external_type_specification]
pub struct ExIoErrorKind(std::io::ErrorKind);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExVarError(std::env::VarError);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExStdout(std::io::Stdout);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExStdoutLock<'a>(std::io::StdoutLock<'a>);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExSystemTimeError(std::time::SystemTimeError);

pub assume_specification<P: AsRef<Path>>[ Path::join::<P> ](p: &Path, q: P) -> PathBuf;

pub assume_specification[ Path::exists ](p: &Path) -> bool;

pub assume_specification[ Path::is_dir ](p: &Path) -> bool;

pub assume_specification[ Path::parent ](p: &Path) -> Option<&Path>;

pub assume_specification[ Path::extension ](p: &Path) -> Option<&OsStr>;

pub assume_specification[ Path::to_path_buf ](p: &Path) -> PathBuf;

pub assume_specification[ Path::display ](p: &Path) -> std::path::Display<'_>;

pub assume_specification[ <PathBuf as core::ops::Deref>::deref ](p: &PathBuf) -> &Path;

pub assume_specification[ OsStr::is_empty ](s: &OsStr) -> bool;

pub assume_specification[ OsStr::to_str ](s: &OsStr) -> Option<&str>;

pub assume_specification<P: AsRef<Path>>[ std::fs::read_to_string::<P> ](p: P) -> std::io::Result<String>;

pub assume_specification<P: AsRef<Path>>[ std::fs::create_dir_all::<P> ](p: P) -> std::io::Result<()>;

pub assume_specification<P: AsRef<Path>>[ std::fs::remove_file::<P> ](p: P) -> std::io::Result<()>;

pub assume_specification<P: AsRef<Path>>[ std::fs::File::open::<P> ](p: P) -> std::io::Result<std::fs::File>;

pub assume_specification[ std::io::stdout ]() -> std::io::Stdout;

pub assume_specification<S: AsRef<OsStr>>[ Path::with_extension::<S> ](p: &Path, ext: S) -> PathBuf;

pub assume_specification<P: AsRef<Path>>[ std::fs::exists::<P> ](p: P) -> std::io::Result<bool>;

pub assume_specification<P: AsRef<Path>, C: AsRef<[u8]>>[ std::fs::write::<P, C> ](p: P, contents: C) -> std::io::Result<()>;

pub assume_specification<K: AsRef<OsStr>>[ std::env::var::<K> ](key: K) -> Result<String, std::env::VarError>;

pub assume_specification<K: AsRef<OsStr>>[ std::env::var_os::<K> ](key: K) -> Option<OsString>;

pub assume_specification[ <std::io::Stdout as std::io::IsTerminal>::is_terminal ](s: &std::io::Stdout) -> bool;


// ---- S26: further paths, files, terminal, io (content-free)

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExMetadata(std::fs::Metadata);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExOpenOptions(std::fs::OpenOptions);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExTryLockError(std::fs::TryLockError);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExStdin(std::io::Stdin);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExStderr(std::io::Stderr);

#[verifier::external_trait_specification]
pub trait ExIoWrite {
    type ExternalTraitSpecificationFor: std::io::Write;

    fn flush(&mut self) -> std::io::Result<()>;

    fn write_all(&mut self, buf: &[u8]) -> std::io::Result<()>;

    fn write_fmt(&mut self, args: core::fmt::Arguments<'_>) -> std::io::Result<()>;
}

pub assume_specification<S: AsRef<OsStr> + ?Sized>[ Path::new::<S> ](s: &S) -> &Path;

pub assume_specification<S: AsRef<OsStr> + ?Sized>[ OsStr::new::<S> ](s: &S) -> &OsStr;

pub assume_specification[ <OsStr as alloc::borrow::ToOwned>::to_owned ](s: &OsStr) -> OsString;

pub assume_specification<P: AsRef<Path>>[ std::fs::File::create::<P> ](p: P) -> std::io::Result<std::fs::File>;

pub assume_specification<P: AsRef<Path>>[ std::fs::remove_dir::<P> ](p: P) -> std::io::Result<()>;

pub assume_specification[ std::fs::Metadata::len ](m: &std::fs::Metadata) -> u64;

pub assume_specification<P: AsRef<Path>>[ std::fs::metadata::<P> ](p: P) -> std::io::Result<std::fs::Metadata>;

pub assume_specification[ std::fs::OpenOptions::new ]() -> std::fs::OpenOptions;

pub assume_specification<'a>[ std::fs::OpenOptions::truncate ](o: &'a mut std::fs::OpenOptions, t: bool) -> &'a mut std::fs::OpenOptions;

pub assume_specification[ std::io::stdin ]() -> std::io::Stdin;

pub assume_specification[ std::io::Stdin::read_line ](s: &std::io::Stdin, buf: &mut String) -> std::io::Result<usize>;

pub assume_specification[ std::io::Stdout::lock ](s: &std::io::Stdout) -> std::io::StdoutLock<'static>;

pub assume_specification[ <std::io::Stdout as std::io::Write>::flush ](s: &mut std::io::Stdout) -> std::io::Result<()>;

pub assume_specification[ <std::io::Stderr as std::io::IsTerminal>::is_terminal ](s: &std::io::Stderr) -> bool;

pub assume_specification<'a>[ <std::io::StdoutLock<'a> as std::io::IsTerminal>::is_terminal ](s: &std::io::StdoutLock<'a>) -> bool;

pub assume_specification[ std::io::stderr ]() -> std::io::Stderr;

pub assume_specification<E: Into<Box<dyn core::error::Error + Send + Sync>>>[ std::io::Error::new::<E> ](kind: std::io::ErrorKind, error: E) -> std::io::Error;

// ---- time: std::time::Instant is opaque; now is arbitrary

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExInstant(std::time::Instant);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExSystemTime(std::time::SystemTime);

pub assume_specification[ std::time::Instant::now ]() -> std::time::Instant;

pub assume_specification[ std::time::Instant::elapsed ](i: &std::time::Instant) -> core::time::Duration;

/// Saturates at zero (it does not panic).
pub assume_specification[ std::time::Instant::duration_since ](i: &std::time::Instant, earlier: std::time::Instant) -> core::time::Duration;

pub assume_specification[ std::time::SystemTime::now ]() -> std::time::SystemTime;

pub assume_specification[ std::time::SystemTime::duration_since ](t: &std::time::SystemTime, earlier: std::time::SystemTime) -> Result<core::time::Duration, std::time::SystemTimeError>;

pub assume_specification<T>[ <std::sync::OnceLock<T> as From<T>>::from ](t: T) -> std::sync::OnceLock<T>;

// ---- S27: io errors, OpenOptions, directories, paths, writes (content-free)

pub assume_specification[ std::io::Error::kind ](e: &std::io::Error) -> std::io::ErrorKind;

pub assume_specification[ std::io::Error::raw_os_error ](e: &std::io::Error) -> Option<i32>;

pub assume_specification<E: Into<Box<dyn core::error::Error + Send + Sync>>>[ std::io::Error::other::<E> ](error: E) -> std::io::Error;

pub assume_specification[ std::fs::File::metadata ](f: &std::fs::File) -> std::io::Result<std::fs::Metadata>;

pub assume_specification<P: AsRef<Path>>[ std::fs::OpenOptions::open::<P> ](o: &std::fs::OpenOptions, p: P) -> std::io::Result<std::fs::File>;

pub assume_specification<'a>[ std::fs::OpenOptions::read ](o: &'a mut std::fs::OpenOptions, b: bool) -> &'a mut std::fs::OpenOptions;

pub assume_specification<'a>[ std::fs::OpenOptions::write ](o: &'a mut std::fs::OpenOptions, b: bool) -> &'a mut std::fs::OpenOptions;

pub assume_specification<'a>[ std::fs::OpenOptions::append ](o: &'a mut std::fs::OpenOptions, b: bool) -> &'a mut std::fs::OpenOptions;

pub assume_specification<'a>[ std::fs::OpenOptions::create ](o: &'a mut std::fs::OpenOptions, b: bool) -> &'a mut std::fs::OpenOptions;

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExFileType(std::fs::FileType);

pub assume_specification<P: AsRef<Path>>[ std::fs::read_dir::<P> ](p: P) -> std::io::Result<std::fs::ReadDir>;

impl super::iter::IteratorSpecImpl for std::fs::ReadDir {
    open spec fn obeys_prophetic_iter_laws(&self) -> bool { false }
    uninterp spec fn remaining(&self) -> Seq<std::io::Result<std::fs::DirEntry>>;
    uninterp spec fn will_return_none(&self) -> bool;
    uninterp spec fn decrease(&self) -> Option<nat>;
    open spec fn peek(&self, index: int) -> Option<std::io::Result<std::fs::DirEntry>> { None }
}

pub assume_specification[ std::fs::DirEntry::path ](d: &std::fs::DirEntry) -> PathBuf;

pub assume_specification[ std::fs::DirEntry::metadata ](d: &std::fs::DirEntry) -> std::io::Result<std::fs::Metadata>;

pub assume_specification[ std::fs::DirEntry::file_type ](d: &std::fs::DirEntry) -> std::io::Result<std::fs::FileType>;

pub assume_specification[ std::fs::Metadata::is_dir ](m: &std::fs::Metadata) -> bool;

pub assume_specification[ std::fs::Metadata::is_file ](m: &std::fs::Metadata) -> bool;

pub assume_specification[ std::fs::Metadata::file_type ](m: &std::fs::Metadata) -> std::fs::FileType;

pub assume_specification[ std::fs::FileType::is_dir ](t: &std::fs::FileType) -> bool;

pub assume_specification[ std::fs::FileType::is_file ](t: &std::fs::FileType) -> bool;

pub assume_specification[ Path::as_os_str ](p: &Path) -> &OsStr;

pub assume_specification[ OsStr::to_string_lossy ](s: &OsStr) -> alloc::borrow::Cow<'_, str>;

pub assume_specification<T: AsRef<OsStr>>[ OsString::push::<T> ](s: &mut OsString, t: T);

pub assume_specification[ std::time::UNIX_EPOCH ] -> std::time::SystemTime;

pub assume_specification[ std::env::consts::OS ] -> &'static str;

pub assume_specification[ <std::io::Stdin as std::io::IsTerminal>::is_terminal ](s: &std::io::Stdin) -> bool;

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(B)]
pub struct ExIoLines<B>(std::io::Lines<B>);

// ---- S28: more fs/io/path (content-free)

pub assume_specification[ std::fs::File::sync_all ](f: &std::fs::File) -> std::io::Result<()>;

pub assume_specification[ std::fs::DirEntry::file_name ](d: &std::fs::DirEntry) -> OsString;

pub assume_specification[ std::io::Error::last_os_error ]() -> std::io::Error;

pub assume_specification[ Path::file_stem ](p: &Path) -> Option<&OsStr>;

pub assume_specification[ Path::file_name ](p: &Path) -> Option<&OsStr>;

pub assume_specification[ std::env::consts::ARCH ] -> &'static str;

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExPermissions(std::fs::Permissions);

#[verifier::external_trait_specification]
pub trait ExOpenOptionsExt {
    type ExternalTraitSpecificationFor: std::os::unix::fs::OpenOptionsExt;

    fn mode(&mut self, mode: u32) -> &mut Self;
}

#[verifier::external_trait_specification]
pub trait ExPermissionsExt {
    type ExternalTraitSpecificationFor: std::os::unix::fs::PermissionsExt;

    fn from_mode(mode: u32) -> Self where Self: Sized;
}

pub assume_specification<P: AsRef<Path>>[ std::fs::set_permissions::<P> ](p: P, perm: std::fs::Permissions) -> std::io::Result<()>;

#[verifier::external_trait_specification]
pub trait ExSeek {
    type ExternalTraitSpecificationFor: std::io::Seek;

    fn seek(&mut self, pos: std::io::SeekFrom) -> std::io::Result<u64>;
}

#[verifier::external_type_specification]
pub struct ExSeekFrom(std::io::SeekFrom);

#[verifier::external_trait_specification]
pub trait ExBufRead: std::io::Read {
    type ExternalTraitSpecificationFor: std::io::BufRead;

    fn lines(self) -> std::io::Lines<Self> where Self: Sized;

    fn read_until(&mut self, byte: u8, buf: &mut alloc::vec::Vec<u8>) -> std::io::Result<usize>;
}

#[verifier::external_trait_specification]
#[verifier::allow(undeclared_external_trait)]
pub trait ExRead {
    type ExternalTraitSpecificationFor: std::io::Read;

    fn read_exact(&mut self, buf: &mut [u8]) -> std::io::Result<()>;
}

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(R)]
pub struct ExBufReader<R: ?Sized>(std::io::BufReader<R>);

pub assume_specification<R: std::io::Read>[ std::io::BufReader::<R>::new ](inner: R) -> std::io::BufReader<R>;

/// `std::fs::rename`: content-free (the file system is not modelled).
pub assume_specification<P: AsRef<std::path::Path>, Q: AsRef<std::path::Path>>[ std::fs::rename ](
    from: P,
    to: Q,
) -> std::io::Result<()>;

/// `std::process::id`: content-free.
pub assume_specification[ std::process::id ]() -> u32;

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
#[verifier::reject_recursive_types(A)]
pub struct ExHashSetIntoIter<T, A: core::alloc::Allocator>(std::collections::hash_set::IntoIter<T, A>);

/// `HashMap`'s consuming iterator: opaque, without iterator laws (like `hash_set::IntoIter`).
#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(V)]
#[verifier::reject_recursive_types(A)]
pub struct ExHashMapIntoIter<K, V, A: core::alloc::Allocator>(std::collections::hash_map::IntoIter<K, V, A>);

} // verus!
