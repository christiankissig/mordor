#!/usr/bin/env python3
"""The web UI in real browsers, on the static build and on mordor-web (W5, #181).

    python3 -I wasm/test/ui_test.py SESSION_NATIVE [--static SITE] [--server SERVER_EXE]
                                    [--browsers chromium,firefox]

--static SITE: wasm/static.sh's directory, served as plain files (Python's
http.server, no special headers). --server SERVER_EXE: mordor-web
(_build/default/web/server.exe), started from the repository's root on a free
port. In each browser, on each:

  runs     parse, visualize and assertions of SB, MP and LB (the CLI's
           samples) from the editor; each must end Complete, with as many
           executions as the native session counts (SESSION_NATIVE);
  examples the example library and the test runner's lists load;
  busy     (static only) while seqlock-1's episodicity runs in the worker, the
           page's timers keep firing: no gap over 250 ms;
  cancel   a run of seqlock-1 is cancelled, and a run after it completes.

Chromium through Playwright (pip install playwright; playwright install
chromium); Firefox through geckodriver (WebDriver), with the system's Firefox.
Exits non-zero on any failure.
"""
import argparse
import functools
import http.server
import json
import os
import socket
import subprocess
import sys
import threading
import time
import urllib.request

REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
SAMPLES = {
    'SB': '\nname = SB\n%%\n{ x := 1 } ||| { y := 1 }\n%% allow (x = 0 && y = 0) []\n  ',
    'MP': '\nname = MP\n%%\n{ x := 1; y := 1 } ||| { r1 := y; r2 := x }\n%% forbid (r1 = 1 && r2 = 0) []\n  ',
    'LB': '\nname = LB\n%%\n{ r1 := x; y := 1 } ||| { r2 := y; x := 1 }\n%% forbid (r1 = 1 && r2 = 1) []\n  ',
}
ACTIONS = ['parse', 'visualize', 'assertions']
SLOW = 'programs/seqlock-1.lit'


def free_port():
    with socket.socket() as s:
        s.bind(('127.0.0.1', 0))
        return s.getsockname()[1]


def serve_static(site):
    port = free_port()
    class Quiet(http.server.SimpleHTTPRequestHandler):
        def log_message(self, *args):
            pass

    handler = functools.partial(Quiet, directory=site)
    httpd = http.server.ThreadingHTTPServer(('127.0.0.1', port), handler)
    threading.Thread(target=httpd.serve_forever, daemon=True).start()
    return f'http://127.0.0.1:{port}/', httpd.shutdown


def serve_mordor_web(server_exe):
    port = free_port()
    proc = subprocess.Popen([os.path.abspath(server_exe)], cwd=REPO,
                            env={**os.environ, 'MORDOR_WEB_PORT': str(port)},
                            stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    url = f'http://127.0.0.1:{port}/'
    for _ in range(100):
        try:
            urllib.request.urlopen(url + 'health', timeout=1)
            return url, proc.terminate
        except OSError:
            time.sleep(0.2)
    proc.terminate()
    raise RuntimeError('mordor-web did not start')


class Chromium:
    def __init__(self):
        from playwright.sync_api import sync_playwright
        self.pw = sync_playwright().start()
        self.browser = self.pw.chromium.launch()
        self.page = self.browser.new_page()

    def goto(self, url):
        self.page.goto(url)

    def run(self, body):
        return self.page.evaluate('() => {' + body + '}')

    def quit(self):
        self.browser.close()
        self.pw.stop()


class Firefox:
    """WebDriver over HTTP to geckodriver, which starts the system's Firefox."""

    def __init__(self):
        self.port = free_port()
        self.proc = subprocess.Popen(['geckodriver', '--port', str(self.port)],
                                     stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        for _ in range(100):
            try:
                caps = {'capabilities': {'alwaysMatch': {
                    'moz:firefoxOptions': {'args': ['-headless']}}}}
                self.session = self.call('POST', '/session', caps)['sessionId']
                return
            except OSError:
                time.sleep(0.2)
        raise RuntimeError('geckodriver did not start')

    def call(self, method, path, body=None):
        request = urllib.request.Request(
            f'http://127.0.0.1:{self.port}{path}', method=method,
            data=None if body is None else json.dumps(body).encode(),
            headers={'Content-Type': 'application/json'})
        with urllib.request.urlopen(request, timeout=600) as response:
            return json.load(response)['value']

    def goto(self, url):
        self.call('POST', f'/session/{self.session}/url', {'url': url})

    def run(self, body):
        return self.call('POST', f'/session/{self.session}/execute/sync',
                         {'script': body, 'args': []})

    def quit(self):
        try:
            self.call('DELETE', f'/session/{self.session}')
        finally:
            self.proc.terminate()


def wait(browser, condition, timeout):
    """Polls the JavaScript expression [condition] until it is true."""
    end = time.monotonic() + timeout
    while time.monotonic() < end:
        if browser.run(f'return !!({condition});'):
            return True
        time.sleep(0.2)
    return False


def start_run(browser, program, action):
    browser.run(f'''
        const gv = window._graphVisualizer;
        gv.currentAction = {json.dumps(action)};
        gv.currentEndpoint = {json.dumps(f'/api/{action}/stream')};
        document.getElementById('litmus-input').value = {json.dumps(program)};
        document.getElementById('action-btn').click();
        return true;''')


STATUS = "document.getElementById('status').textContent"


def native_executions(session_native, program, action):
    out = subprocess.run([session_native, action], input=json.dumps({'program': program}),
                         capture_output=True, text=True, check=True).stdout
    for frame in out.split('\n\n'):
        if frame.startswith('data: '):
            message = json.loads(frame[6:])
            if message.get('type') == 'complete':
                return message['total_executions']
    return None


def check(browser, url, session_native, static, failures, label):
    def fail(what):
        failures.append(f'{label}: {what}')
        print(f'  FAIL {what}', flush=True)

    browser.goto(url)
    if not wait(browser, "document.querySelectorAll('#examples option').length > 1", 60):
        fail('the example library did not load')
    for name, program in SAMPLES.items():
        for action in ACTIONS:
            start = time.monotonic()
            start_run(browser, program, action)
            if not wait(browser, f"{STATUS} !== 'Processing...' && "
                                 "!document.getElementById('action-btn').disabled", 300):
                fail(f'{action} {name}: did not finish')
                continue
            status = browser.run(f'return {STATUS};')
            count = browser.run("return Number(document.getElementById('execution-count').textContent);")
            expected = native_executions(session_native, program, action)
            ok = status == 'Complete' and (expected is None or count == expected)
            print(f'  {action:10} {name}: {status}, {count} executions (native {expected}), '
                  f'{time.monotonic() - start:.1f}s', flush=True)
            if not ok:
                fail(f'{action} {name}: {status}, {count} executions, native {expected}')

    browser.run('''
        Promise.all([
            MordorTransport.getJSON('/api/tests/list'),
            MordorTransport.getJSON('/api/episodicity/list')])
          .then(([t, e]) => { window.__lists = [t.tests.length, e.tests.length]; });
        return true;''')
    wait(browser, 'window.__lists', 30)
    lists = browser.run('return window.__lists || [0, 0];')
    print(f'  test runner lists: {lists[0]} litmus tests, {lists[1]} episodicity tests', flush=True)
    if not lists[0] or not lists[1]:
        fail('the test runner lists are empty')

    # The test runner's Run, of a litmus test and of an episodicity test.
    browser.run('''
        Promise.all([
            MordorTransport.runTest('litmus', 'litmus-tests/test6/MP.lit'),
            MordorTransport.runTest('episodicity', 'programs/episodicity/register_condition/fail.lit')])
          .then(([l, e]) => { window.__runs = [l.success, l.valid, e.success, e.loops_analyzed, e.all_episodic]; },
                (err) => { window.__runs = [String(err)]; });
        return true;''')
    wait(browser, 'window.__runs', 300)
    runs = browser.run('return window.__runs || null;')
    print(f'  test runner runs: MP success, valid {runs[:2]}; '
          f'register_condition/fail success, loops, all episodic {runs[2:]}', flush=True)
    if runs != [True, True, True, 1, False]:
        fail(f'test runner runs: {runs}')

    with open(os.path.join(REPO, SLOW)) as f:
        slow = f.read()
    if static:
        browser.run('''
            window.__gaps = [];
            let last = performance.now();
            window.__ticker = setInterval(() => {
                const now = performance.now();
                window.__gaps.push(now - last);
                last = now;
            }, 50);
            return true;''')
        start = time.monotonic()
        start_run(browser, slow, 'episodicity')
        finished = wait(browser, f"{STATUS} !== 'Processing...'", 600)
        gap = browser.run('clearInterval(window.__ticker); return Math.max(...window.__gaps);')
        print(f'  busy: {SLOW} episodicity {browser.run(f"return {STATUS};")} in '
              f'{time.monotonic() - start:.1f}s; longest gap between timer ticks {gap:.0f} ms',
              flush=True)
        if not finished or gap > 250:
            fail(f'busy: finished {finished}, longest gap {gap:.0f} ms')

    start_run(browser, slow, 'visualize')
    time.sleep(3)
    browser.run("document.getElementById('cancel-btn').click(); return true;")
    cancelled = wait(browser, f"{STATUS} === 'Cancelled'", 5)
    start_run(browser, SAMPLES['SB'], 'visualize')
    after = wait(browser, f"{STATUS} === 'Complete'", 120)
    print(f'  cancel: cancelled {cancelled}, a run after it completed {after}', flush=True)
    if not (cancelled and after):
        fail(f'cancel: cancelled {cancelled}, run after {after}')


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('session_native')
    parser.add_argument('--static')
    parser.add_argument('--server')
    parser.add_argument('--browsers', default='chromium,firefox')
    args = parser.parse_args()
    failures = []
    targets = []
    if args.static:
        targets.append(('static', serve_static(args.static), True))
    if args.server:
        targets.append(('mordor-web', serve_mordor_web(args.server), False))
    try:
        for name in args.browsers.split(','):
            for target, (url, _), static in targets:
                print(f'{name}, {target} ({url})', flush=True)
                browser = Chromium() if name == 'chromium' else Firefox()
                try:
                    check(browser, url, args.session_native, static, failures, f'{name} {target}')
                finally:
                    browser.quit()
    finally:
        for _, (_, stop), _ in targets:
            stop()
    print('ok' if not failures else f'{len(failures)} failures')
    return 1 if failures else 0


if __name__ == '__main__':
    sys.exit(main())
