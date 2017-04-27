const os = require('os');
const test = require('ava-spec').test;
const co = require('co');
const cpp = require('child-process-promise');
const fsp = require('fs-promise');
const glob = require('glob-promise');
const throat = require('throat')(os.cpus().length);

function compareText(a, b) {
	let a1 = a.trim().split(/\r?\n/g).join('\n');
	let b1 = b.trim().split(/\r?\n/g).join('\n');
	return a1 === b1;
}

test('Test framework actually works.', t => t.pass());

test.group("Idris-codegen-js", test => co(function* () {
	let files = yield glob('tests/*.idr');
	for (let idr of files) {
		test(idr, function* (t) {
			const jspath = idr.replace(/\.idr$/, '.js')
			const trpath = idr.replace(/\.idr$/, '.testres')
			const compile = yield throat(() => cpp.spawn('idris', [
				'--codegen', 'es',
				'-p', 'effects',
				'-p', 'js',
				'-o', jspath,
				idr
			]));
			const run = yield cpp.spawn(process.argv[0], [jspath], { capture: ['stdout'] });
			const tr = yield fsp.readFile(trpath, 'utf-8');
			t.true(compareText(run.stdout, tr));
		})
	}
}));
