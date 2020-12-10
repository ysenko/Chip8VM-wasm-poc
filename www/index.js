import {new_vm} from "chip8-wasm"
import {memory} from "chip8-wasm/chip8_wasm_bg.wasm";

const vm = new_vm();

const ENABLED_PIXEL = 255;
const DISPLAY_WIDTH = vm.get_display_width();
const DISPLAY_HEIGHT = vm.get_display_height();

const display = document.getElementById("display");
const displayCtx = display.getContext("2d");

const initDisplay = () => {
    display.width = DISPLAY_WIDTH;
    display.height = DISPLAY_HEIGHT;
};

const enablePixel = (frameData, pixelIdx) => {
    for (let offset=0; offset<4; offset++) {
        frameData.data[pixelIdx*4 + offset] = ENABLED_PIXEL;
    }
    return frameData.data
};

const getIdx = (row, col) => {
    return row * DISPLAY_WIDTH + col;
};

const isPixelSet = (idx, frameData) => {
    const byteOffset = Math.floor(idx / 8);
    const bitMask = 1 << (idx % 8);
    return (frameData[byteOffset] & bitMask) === bitMask;
}

const drawFrame = () => {
    const videoPortPtr = vm.video_port();
    const frameData = new Uint8Array(memory.buffer, videoPortPtr, DISPLAY_WIDTH * DISPLAY_HEIGHT / 8);
    const newFrame = displayCtx.createImageData(DISPLAY_WIDTH, DISPLAY_WIDTH);

    for (let row = 0; row < DISPLAY_HEIGHT; row++) {
        for (let col = 0; col < DISPLAY_WIDTH; col++) {
            const idx = getIdx(row, col);

            if (isPixelSet(idx, frameData)) {
                enablePixel(newFrame, idx);
            }
        }
    }
    displayCtx.putImageData(newFrame, 0, 0);
};

const runForever = (_ts) => {
    if (vm.is_rom_loaded()) {
        vm.tick();
        drawFrame();
    };
    window.requestAnimationFrame(runForever);
};

const fileSelector = document.getElementById("rom_selector");
fileSelector.addEventListener("change", (evt) => {
    const romFile = evt.target.files[0];
    loadRom(romFile);
});

const loadRom = (file) => {
    const reader  = new FileReader();
    reader.addEventListener("load", (evt) => {
        let rom = new Uint8Array(evt.target.result);
        vm.load_rom(rom);
        runForever();
    });
    reader.readAsArrayBuffer(file);
};

const toArrayBuffer = (buffer) => {
    let arrayBuff = new ArrayBuffer(buffer.length);
    let view = new Uint8Array(arrayBuff);
    for (let i=0; i<buffer.length; i++) {
        view[i] = buffer[i];
    }
    return arrayBuff;
};

// const rom = new Uint16Array([
//     0x6002, // Load 2 in V0
//     0x7002, // Add 2 to V0
//     0xF029, // Load location of sprite 4 into I
//     0xDAA5, // Draw 4 on 0xA 0xA coordinates
// ]);
// vm.load_rom(rom);

window.onload = (_evt) => {
    initDisplay();
    window.requestAnimationFrame(runForever);
};
