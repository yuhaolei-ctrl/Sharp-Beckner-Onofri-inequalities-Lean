#!/usr/bin/env python3
"""Resource/observability patch only: 1 GiB worker stacks and optional name traces.
The declaration checker and its logical rules are not changed.
"""
import argparse
from pathlib import Path

p = argparse.ArgumentParser()
p.add_argument('source', type=Path)
args = p.parse_args()
lib = args.source / 'src/lib.rs'
s = lib.read_text()
old = next((x for x in ('STACK_SIZE: usize = 16_777_216;', 'STACK_SIZE: usize = 268_435_456;') if x in s), None)
assert old is not None and s.count(old) == 1
lib.write_text(s.replace(old, 'STACK_SIZE: usize = 1_073_741_824;'))
p = args.source / 'src/tc.rs'
s = p.read_text()
old = '''            for i in 0..num_threads {
                handles.push(
                    thread::Builder::new()
                        .name(format!("thread_{}", i))
                        .stack_size(crate::STACK_SIZE)
                        .spawn_scoped(sco, || loop {
                            let idx = task_num.fetch_add(1, Relaxed);
                            if let Some((_, declar)) = self.declars.get_index(idx) {
                                self.check_declar(declar);
                            } else {
                                break
                            }
                        })
                        .unwrap(),
                )
            }'''
new = '''            for i in 0..num_threads {
                let task_num = &task_num;
                handles.push(
                    thread::Builder::new()
                        .name(format!("thread_{}", i))
                        .stack_size(crate::STACK_SIZE)
                        .spawn_scoped(sco, move || {
                            use std::io::Write;
                            let mut trace = std::env::var_os("NANODA_TRACE_DIR").map(|dir| {
                                let path = std::path::PathBuf::from(dir)
                                    .join(format!("nanoda-thread-{}.trace", i));
                                std::fs::File::create(path).expect("create diagnostic trace")
                            });
                            loop {
                                let idx = task_num.fetch_add(1, Relaxed);
                                if let Some((_, declar)) = self.declars.get_index(idx) {
                                    if let Some(file) = trace.as_mut() {
                                        let entry = self.with_ctx(|ctx| format!("{} {:?}\\n", idx,
                                            ctx.debug_print(declar.info().name)));
                                        file.write_all(entry.as_bytes()).expect("write diagnostic trace");
                                    }
                                    self.check_declar(declar);
                                } else {
                                    break
                                }
                            }
                        })
                        .unwrap(),
                )
            }'''
assert s.count(old) == 1
p.write_text(s.replace(old, new))
print('Applied runtime-only stack and diagnostic-trace patch; checker rules unchanged.')
