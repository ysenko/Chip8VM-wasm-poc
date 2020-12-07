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

    requestAnimationFrame(drawFrame);
};

const runForever = () => {
    drawFrame();
};

vm.load_rom(new Uint8Array([0x6002, 0x7002, 0xF029, 0xDAA5]));

window.onload = (_evt) => {
    initDisplay();
    runForever();
};
