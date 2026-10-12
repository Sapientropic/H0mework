import { defineConfig } from "astro/config";

export default defineConfig({
  // Pages read ../docs and ../papers at build time; nothing is copied into the site.
  vite: { server: { fs: { allow: [".."] } } },
});
