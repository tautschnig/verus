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

} // verus!
