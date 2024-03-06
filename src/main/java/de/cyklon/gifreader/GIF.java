package de.cyklon.gifreader;

import org.jetbrains.annotations.NotNull;

import java.awt.*;
import java.awt.image.BufferedImage;
import java.awt.image.DataBufferInt;
import java.io.BufferedInputStream;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.net.MalformedURLException;
import java.net.URL;
import java.util.ArrayList;
import java.util.List;

public class GIF {

	private final List<Frame> frames;
	private final int width, height;
	private final int loopCount;


	protected GIF(List<Frame> frames, int width, int height, int loopCount) {
		this.frames = frames;
		this.width = width;
		this.height = height;
		this.loopCount = loopCount;
	}

	public List<Frame> getFrames() {
		return frames;
	}

	public int getFrameCount() {
		return frames.size();
	}

	public int getWidth() {
		return width;
	}

	public int getHeight() {
		return height;
	}

	public Dimension getDimension() {
		return new Dimension(width, height);
	}
	/**
	 * @return the loopCount. 0 means infinite
	 */
	public int getLoopCount() {
		return loopCount;
	}

	@Override
	public boolean equals(Object o) {
		return o instanceof GIF g && g.frames.equals(frames) && g.width==width && g.height==height && g.loopCount==loopCount;
	}

	@Override
	public int hashCode() {
		int result = frames.hashCode();
		result = 31 * result + width;
		result = 31 * result + height;
		result = 31 * result + loopCount;
		return result;
	}

	@Override
	public String toString() {
		return "GIF{" +
				"frames=" + frames +
				", width=" + width +
				", height=" + height +
				", loopCount=" + loopCount +
				'}';
	}

	public record Frame(BufferedImage image, int delay) {
		@Override
		public boolean equals(Object obj) {
			return obj instanceof Frame f && f.image().equals(image) && f.delay()==delay;
		}

		@Override
		public int hashCode() {
			int result = image.hashCode();
			result = 31 * result + delay;
			return result;
		}

		@Override
		public String toString() {
			return "Frame{" +
					"image=" + image +
					", delay=" + delay +
					'}';
		}
	}


	public static GIF read(@NotNull String name) throws IOException {
		name = name.strip().toLowerCase();
		InputStream in;
		if (name.contains("file:") || name.contains(":/")) {
			URL url;
			try {
				url = new URL(name);
			} catch (MalformedURLException e) {
				throw new IOException(e);
			}
			in = url.openStream();
		} else {
			in = new FileInputStream(name);
		}
		try(in) {
			return read(in);
		}
	}
	public static GIF read(@NotNull InputStream in) throws IOException {
		return new Decoder().read(in);
	}

	private final static class Decoder {

		private final byte[] block = new byte[256];
		private int blockSize = 0;

		public GIF read(@NotNull InputStream in) throws IOException {
			if (!(in instanceof BufferedInputStream))
				in = new BufferedInputStream(in);

			int width;
			int height;
			boolean gctFlag;
			int gctSize;
			int loopCount = 1;

			int[] gct = null;
			int[] lct;
			int[] act;

			int bgIndex;
			int bgColor = 0;
			int lastBgColor = 0;

			boolean lctFlag;
			boolean interlace;
			int lctSize;

			int ix, iy, iw, ih;
			Rectangle lastRect = null;
			BufferedImage image;
			BufferedImage lastImage = null;

			int dispose = 0;
			int lastDispose = 0;
			boolean transparency = false;
			int delay = 0;
			int transIndex = 0;

			final int MaxStackSize = 4096;

			short[] prefix = null;
			byte[] suffix = null;
			byte[] pixelStack = null;
			byte[] pixels = null;

			List<Frame> frames = new ArrayList<>();
			int frameCount = 0;

			//read Header
			StringBuilder id = new StringBuilder();
			for (int i = 0; i < 6; i++) {
				id.append((char) in.read());
			}
			if (!id.toString().startsWith("GIF")) throw new IOException("Invalid Format");

			//Read LSD (Logical Screen Descriptor)

			width = readShort(in);
			height = readShort(in);

			int packed = in.read();
			gctFlag = (packed & 0x80) != 0;

			gctSize = 2 << (packed & 7);

			bgIndex = in.read();
			in.read();

			if (gctFlag) {
				gct = readColorTable(in, gctSize);
				bgColor = gct[bgIndex];
			}

			// read GIF file content blocks
			boolean done = false;
			while (!done) {
				int code = in.read();
				switch (code) {

					case 0x2C -> {
						//read image
						ix = readShort(in);
						iy = readShort(in);
						iw = readShort(in);
						ih = readShort(in);

						packed = in.read();
						lctFlag = (packed & 0x80) != 0;
						interlace = (packed & 0x40) != 0;

						lctSize = 2 << (packed & 7);

						if (lctFlag) {
							lct = readColorTable(in, lctSize);
							act = lct;
						} else {
							act = gct;
							if (bgIndex == transIndex)
								bgColor = 0;
						}
						int save = 0;
						if (transparency) {
							save = act[transIndex];
							act[transIndex] = 0;
						}

						if (act == null) throw new IOException("Invalid Format");

						//decode image data
						int NullCode = -1;
						int npix = iw * ih;
						int available,
								clear,
								code_mask,
								code_size,
								end_of_information,
								in_code,
								old_code,
								bits,
								count,
								i,
								datum,
								data_size,
								first,
								top,
								bi,
								pi;

						if ((pixels == null) || (pixels.length < npix)) {
							pixels = new byte[npix];
						}
						if (prefix == null) prefix = new short[MaxStackSize];
						if (suffix == null) suffix = new byte[MaxStackSize];
						if (pixelStack == null) pixelStack = new byte[MaxStackSize + 1];

						//  Initialize GIF data stream decoder.

						data_size = in.read();
						clear = 1 << data_size;
						end_of_information = clear + 1;
						available = clear + 2;
						old_code = NullCode;
						code_size = data_size + 1;
						code_mask = (1 << code_size) - 1;
						for (code = 0; code < clear; code++) {
							prefix[code] = 0;
							suffix[code] = (byte) code;
						}

						//  Decode GIF pixel stream.

						datum = bits = count = first = top = pi = bi = 0;

						for (i = 0; i < npix; ) {
							if (top == 0) {
								if (bits < code_size) {
									if (count == 0) {
										count = readBlock(in);
										if (count <= 0)
											break;
										bi = 0;
									}
									datum += (((int) block[bi]) & 0xff) << bits;
									bits += 8;
									bi++;
									count--;
									continue;
								}

								code = datum & code_mask;
								datum >>= code_size;
								bits -= code_size;

								if ((code > available) || (code == end_of_information))
									break;
								if (code == clear) {
									//  Reset decoder.
									code_size = data_size + 1;
									code_mask = (1 << code_size) - 1;
									available = clear + 2;
									old_code = NullCode;
									continue;
								}
								if (old_code == NullCode) {
									pixelStack[top++] = suffix[code];
									old_code = code;
									first = code;
									continue;
								}
								in_code = code;
								if (code == available) {
									pixelStack[top++] = (byte) first;
									code = old_code;
								}
								while (code > clear) {
									pixelStack[top++] = suffix[code];
									code = prefix[code];
								}
								first = ((int) suffix[code]) & 0xff;

								if (available >= MaxStackSize) {
									pixelStack[top++] = (byte) first;
									continue;
								}
								pixelStack[top++] = (byte) first;
								prefix[available] = (short) old_code;
								suffix[available] = (byte) first;
								available++;
								if (((available & code_mask) == 0)
										&& (available < MaxStackSize)) {
									code_size++;
									code_mask += available;
								}
								old_code = in_code;
							}

							top--;
							pixels[pi++] = pixelStack[top];
							i++;
						}

						for (i = pi; i < npix; i++) {
							pixels[i] = 0;
						}

						skip(in);

						frameCount++;

						image = new BufferedImage(width, height, BufferedImage.TYPE_INT_ARGB_PRE);

						int[] dest =
								((DataBufferInt) image.getRaster().getDataBuffer()).getData();

						if (lastDispose > 0) {
							if (lastDispose == 3) {
								int n = frameCount - 2;
								if (n > 0) {
									lastImage = frames.get(n - 1).image();
								} else {
									lastImage = null;
								}
							}

							if (lastImage != null) {
								int[] prev =
										((DataBufferInt) lastImage.getRaster().getDataBuffer()).getData();
								System.arraycopy(prev, 0, dest, 0, width * height);

								if (lastDispose == 2) {
									Graphics2D g = image.createGraphics();
									Color c;
									if (transparency) {
										c = new Color(0, 0, 0, 0);
									} else {
										c = new Color(lastBgColor);
									}
									g.setColor(c);
									g.setComposite(AlphaComposite.Src);
									g.fill(lastRect);
									g.dispose();
								}
							}
						}

						int pass = 1;
						int inc = 8;
						int iline = 0;
						for (int ib = 0; ib < ih; ib++) {
							int line = ib;
							if (interlace) {
								if (iline >= ih) {
									pass++;
									switch (pass) {
										case 2 -> iline = 4;

										case 3 -> {
											iline = 2;
											inc = 4;
										}

										case 4 -> {
											iline = 1;
											inc = 2;
										}
									}
								}
								line = iline;
								iline += inc;
							}
							line += iy;
							if (line < height) {
								int k = line * width;
								int dx = k + ix;
								int dlim = dx + iw;
								if ((k + width) < dlim) {
									dlim = k + width;
								}
								int sx = ib * iw;
								while (dx < dlim) {
									int index = ((int) pixels[sx++]) & 0xff;
									int c = act[index];
									if (c != 0) {
										dest[dx] = c;
									}
									dx++;
								}
							}
						}

						frames.add(new Frame(image, delay));

						if (transparency) act[transIndex] = save;


						//reset frame
						lastDispose = dispose;
						lastRect = new Rectangle(ix, iy, iw, ih);
						lastImage = image;
						lastBgColor = bgColor;
					}

					case 0x21 -> { // extension
						code = in.read();
						switch (code) {
							case 0xf9 -> { // graphics control extension
								in.read(); // block size
								packed = in.read();
								dispose = (packed & 0x1c) >> 2;
								if (dispose == 0) dispose = 1;
								transparency = (packed & 1) != 0;
								delay = readShort(in) * 10;
								transIndex = in.read();
								in.read(); // block terminator
							}

							case 0xff -> { // application extension
								readBlock(in);
								StringBuilder app = new StringBuilder();
								for (int i = 0; i < 11; i++) {
									app.append((char) block[i]);
								}
								if (app.toString().equals("NETSCAPE2.0")) {
									do {
										readBlock(in);
										if (block[0] == 1) {
											int b1 = ((int) block[1]) & 0xff;
											int b2 = ((int) block[2]) & 0xff;
											loopCount = (b2 << 8) | b1;
										}
									} while (blockSize > 0);
								} else skip(in);
							}

							default -> skip(in);
						}
					}

					// terminator
					case 0x3b -> done = true;

					case 0x00 -> {}

					default -> throw new IOException("Invalid Format");
				}
			}

			if (frameCount < 0) throw new IOException("Invalid Format");

			return new GIF(frames, width, height, loopCount);
		}

		private int readBlock(InputStream in) throws IOException {
			blockSize = in.read();
			int n = 0;
			if (blockSize > 0) {
				try {
					int count;
					while (n < blockSize) {
						count = in.read(block, n, blockSize - n);
						if (count == -1)
							break;
						n += count;
					}
				} catch (IOException e) {
					throw new IOException("Invalid Format", e);
				}

				if (n < blockSize) throw new IOException("Invalid Format");
			}
			return n;
		}

		private int[] readColorTable(InputStream in, int ncolors) throws IOException {
			int nbytes = 3 * ncolors;
			int[] tab;
			byte[] c = new byte[nbytes];
			int n;
			try {
				n = in.read(c);
			} catch (IOException e) {
				throw new IOException("Invalid Format", e);
			}
			if (n < nbytes) throw new IOException("Invalid Format");
			else {
				tab = new int[256];
				int i = 0;
				int j = 0;
				while (i < ncolors) {
					int r = ((int) c[j++]) & 0xff;
					int g = ((int) c[j++]) & 0xff;
					int b = ((int) c[j++]) & 0xff;
					tab[i++] = 0xff000000 | (r << 16) | (g << 8) | b;
				}
			}
			return tab;
		}

		private int readShort(InputStream in) throws IOException {
			return in.read() | (in.read() << 8);
		}

		private void skip(InputStream in) throws IOException {
			do {
				readBlock(in);
			} while (blockSize > 0);
		}
	}
}
