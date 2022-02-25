const path = require('path');
const assert = require('assert');
const fs = require('fs');
const {spawnSync} = require('child_process');

const rapidSnark = path.resolve(__dirname,  '../build/prover');
const snarkJs = 'snarkjs';
let temporalFiles = [];

function cleanFiles(files) {
  const cleanAllTemporalFiles = (files === true);
  if (cleanAllTemporalFiles) {
    files = temporalFiles;
    temporalFiles = [];
  }
  files.forEach((file) => {
    if (fs.existsSync(file)) {
      fs.unlinkSync(file);
    }
    if (!cleanAllTemporalFiles) {
      temporalFiles.push(file);
    }
  });
}

function proofGenerationAndVerification(name, prefix, timeout) {
  const bdir = path.resolve(__dirname, name);
  const label = prefix.toUpperCase();
  const publicFile = path.resolve(bdir, `${prefix}_public.json`);
  const proofFile = path.resolve(bdir, `${prefix}_proof.json`);
  timeout = timeout || 5000;

  cleanFiles([publicFile, proofFile]);
  it(`${label} proof generation`, () => {
    assert.equal(0, spawnSync(rapidSnark, [path.resolve(bdir, `${prefix}_circuit.zkey`), 
                                           path.resolve(bdir, 'witness.wtns'), 
                                           proofFile, publicFile]).status);
    assert.equal(true, fs.existsSync(proofFile));
    assert.equal(true, fs.existsSync(publicFile));
  }).timeout(timeout);
  it(`${label} proof verification`, () => {
    assert.equal(0, spawnSync(snarkJs, [prefix, 'verify',
                                        path.resolve(bdir, `${prefix}_verification_key.json`), 
                                        publicFile, proofFile]).status);
  }).timeout(timeout);
}

function Groth16AndPlonkProofGenerationAndVerification(name, timeout) {
  proofGenerationAndVerification(name, 'groth16', timeout);
  proofGenerationAndVerification(name, 'plonk', timeout);
}

describe('build and verify proofs', () => {
  ['basic', 'mux4_1', 'poseidon3', 'poseidon6', 'smtprocessor10'].forEach( (name) => 
      describe(`build and verify proof ${name}`, 
        () => Groth16AndPlonkProofGenerationAndVerification(name, 30*1000)));
});

function cleanUpOnExit() {
  cleanFiles(true);
};

function cleanUpOnExitAndExit() {
  cleanUpOnExit();
  process.exit();
}

process.on('exit', cleanUpOnExit);
process.on('SIGINT', cleanUpOnExitAndExit);
process.on('uncaughtException', cleanUpOnExitAndExit);