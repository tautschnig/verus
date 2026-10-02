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

#[verifier::external_type_specification]
#[verifier::external_body]
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

pub assume_specification[ <std::io::Stdout as std::io::IsTerminal>::is_terminal ](s: &std::io::Stdout) -> bool;

} // verus!
