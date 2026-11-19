//! A prover behind the protocol: a server process that reads requests and writes responses.

use crate::protocol::{Answer, File, Hello, Question, Request, Response};
use std::io::{BufRead, BufReader, Write};
use std::process::{Child, ChildStdin, ChildStdout, Command, Stdio};

pub type Result<T> = std::result::Result<T, String>;

pub trait Prover {
    fn hello(&mut self) -> Result<Hello>;
    fn load(&mut self, file: &str) -> Result<File>;
    /// All questions go out at once; the server may answer them in any order.
    fn ask(&mut self, questions: &[Question]) -> Result<Vec<Answer>>;
}

pub struct Server {
    child: Child,
    input: ChildStdin,
    output: BufReader<ChildStdout>,
}

impl Server {
    pub fn start(command: &[String]) -> Result<Server> {
        let (program, args) = command.split_first().ok_or("empty server command")?;
        let mut child = Command::new(program)
            .args(args)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()
            .map_err(|e| format!("cannot start {program}: {e}"))?;
        let input = child.stdin.take().unwrap();
        let output = BufReader::new(child.stdout.take().unwrap());
        Ok(Server {
            child,
            input,
            output,
        })
    }

    fn send(&mut self, request: &Request) -> Result<()> {
        let line = serde_json::to_string(request).map_err(|e| e.to_string())?;
        writeln!(self.input, "{line}")
            .and_then(|_| self.input.flush())
            .map_err(|e| format!("server gone: {e}"))
    }

    fn receive(&mut self) -> Result<Response> {
        let mut line = String::new();
        match self.output.read_line(&mut line) {
            Ok(0) => Err("server closed its output".to_string()),
            Ok(_) => match serde_json::from_str(&line)
                .map_err(|e| format!("bad response {line:?}: {e}"))?
            {
                Response::Error { message } => Err(message),
                response => Ok(response),
            },
            Err(e) => Err(format!("server gone: {e}")),
        }
    }
}

impl Prover for Server {
    fn hello(&mut self) -> Result<Hello> {
        self.send(&Request::Hello)?;
        match self.receive()? {
            Response::Hello { hello } => Ok(hello),
            other => Err(format!("expected hello, got {other:?}")),
        }
    }

    fn load(&mut self, file: &str) -> Result<File> {
        self.send(&Request::Load {
            file: file.to_string(),
        })?;
        match self.receive()? {
            Response::Loaded { file } => Ok(file),
            other => Err(format!("expected loaded, got {other:?}")),
        }
    }

    fn ask(&mut self, questions: &[Question]) -> Result<Vec<Answer>> {
        for question in questions {
            self.send(&Request::Ask {
                question: question.clone(),
            })?;
        }
        let mut answers = Vec::new();
        while answers.len() < questions.len() {
            match self.receive()? {
                Response::Answer { answer } => answers.push(answer),
                other => return Err(format!("expected answer, got {other:?}")),
            }
        }
        Ok(answers)
    }
}

impl Drop for Server {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}
